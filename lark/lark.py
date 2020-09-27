from __future__ import absolute_import

import sys, os, pickle, hashlib
from io import open


from .utils import STRING_TYPE, Serialize, SerializeMemoizer, FS, isascii, logger
from .load_grammar import load_grammar, FromPackageLoader
from .tree import Tree
from .common import LexerConf, ParserConf

from .lexer import Lexer, TraditionalLexer, TerminalDef, UnexpectedToken
from .parse_tree_builder import ParseTreeBuilder
from .parser_frontends import get_frontend, _get_lexer_callbacks
from .grammar import Rule

import re
try:
    import regex
except ImportError:
    regex = None

###{standalone

class LarkOptions(Serialize):
    """Specifies the options for Lark

    """
    OPTIONS_DOC = """
    **===  General Options  ===**

    start
            The start symbol. Either a string, or a list of strings for multiple possible starts (Default: "start")
    debug
            Display debug information, such as warnings (default: False)
    transformer
            Applies the transformer to every parse tree (equivlent to applying it after the parse, but faster)
    propagate_positions
            Propagates (line, column, end_line, end_column) attributes into all tree branches.
    maybe_placeholders
            When True, the ``[]`` operator returns ``None`` when not matched.

            When ``False``,  ``[]`` behaves like the ``?`` operator, and returns no value at all.
            (default= ``False``. Recommended to set to ``True``)
    cache
            Cache the results of the Lark grammar analysis, for x2 to x3 faster loading. LALR only for now.

            - When ``False``, does nothing (default)
            - When ``True``, caches to a temporary file in the local directory
            - When given a string, caches to the path pointed by the string
    regex
            When True, uses the ``regex`` module instead of the stdlib ``re``.
    g_regex_flags
            Flags that are applied to all terminals (both regex and strings)
    keep_all_tokens
            Prevent the tree builder from automagically removing "punctuation" tokens (default: False)
    tree_class
            Lark will produce trees comprised of instances of this class instead of the default ``lark.Tree``.

    **=== Algorithm Options ===**

    parser
            Decides which parser engine to use. Accepts "earley" or "lalr". (Default: "earley").
            (there is also a "cyk" option for legacy)
    lexer
            Decides whether or not to use a lexer stage

            - "auto" (default): Choose for me based on the parser
            - "standard": Use a standard lexer
            - "contextual": Stronger lexer (only works with parser="lalr")
            - "dynamic": Flexible and powerful (only with parser="earley")
            - "dynamic_complete": Same as dynamic, but tries *every* variation of tokenizing possible.
    ambiguity
            Decides how to handle ambiguity in the parse. Only relevant if parser="earley"

            - "resolve": The parser will automatically choose the simplest derivation
              (it chooses consistently: greedy for tokens, non-greedy for rules)
            - "explicit": The parser will return all derivations wrapped in "_ambig" tree nodes (i.e. a forest).
            - "forest": The parser will return the root of the shared packed parse forest.

    **=== Misc. / Domain Specific Options ===**

    postlex
            Lexer post-processing (Default: None) Only works with the standard and contextual lexers.
    priority
            How priorities should be evaluated - auto, none, normal, invert (Default: auto)
    lexer_callbacks
            Dictionary of callbacks for the lexer. May alter tokens during lexing. Use with caution.
    use_bytes
            Accept an input of type ``bytes`` instead of ``str`` (Python 3 only).
    edit_terminals
            A callback for editing the terminals before parse.
    import_sources
            A List of either paths or loader functions to specify from where grammars are imported 
    source
            Override the source of from where the grammar was loaded. Usefull for relative imports and unconventional grammar loading

    **=== End Options ===**
    """
    if __doc__:
        __doc__ += OPTIONS_DOC

    _defaults = {
        'debug': False,
        'keep_all_tokens': False,
        'tree_class': None,
        'cache': False,
        'postlex': None,
        'parser': 'earley',
        'lexer': 'auto',
        'transformer': None,
        'start': 'start',
        'priority': 'auto',
        'ambiguity': 'auto',
        'regex': False,
        'propagate_positions': False,
        'lexer_callbacks': {},
        'maybe_placeholders': False,
        'edit_terminals': None,
        'g_regex_flags': 0,
        'use_bytes': False,
        'import_sources': [],
        'source': None,
    }

    def __init__(self, options_dict):
        o = dict(options_dict)

        options = {}
        for name, default in self._defaults.items():
            if name in o:
                value = o.pop(name)
                if isinstance(default, bool) and name not in ('cache', 'use_bytes'):
                    value = bool(value)
            else:
                value = default

            options[name] = value

        if isinstance(options['start'], STRING_TYPE):
            options['start'] = [options['start']]

        self.__dict__['options'] = options

        assert self.parser in ('earley', 'lalr', 'cyk', None)

        if self.parser == 'earley' and self.transformer:
            raise ValueError('Cannot specify an embedded transformer when using the Earley algorithm.'
                             'Please use your transformer on the resulting parse tree, or use a different algorithm (i.e. LALR)')

        if o:
            raise ValueError("Unknown options: %s" % o.keys())

    def __getattr__(self, name):
        try:
            return self.options[name]
        except KeyError as e:
            raise AttributeError(e)

    def __setattr__(self, name, value):
        assert name in self.options
        self.options[name] = value

    def serialize(self, memo):
        return self.options

    @classmethod
    def deserialize(cls, data, memo):
        return cls(data)


class Lark(Serialize):
    """Main interface for the library.

    It's mostly a thin wrapper for the many different parsers, and for the tree constructor.

    Parameters:
        grammar: a string or file-object containing the grammar spec (using Lark's ebnf syntax)
        options: a dictionary controlling various aspects of Lark.

    Example:
        >>> Lark(r'''start: "foo" ''')
        Lark(...)
    """
    def __init__(self, grammar, **options):
        self.options = LarkOptions(options)

        # Set regex or re module
        use_regex = self.options.regex
        if use_regex:
            if regex:
                re_module = regex
            else:
                raise ImportError('`regex` module must be installed if calling `Lark(regex=True)`.')
        else:
            re_module = re

        # Some, but not all file-like objects have a 'name' attribute
        if self.options.source is None:
            try:
                self.source = grammar.name
            except AttributeError:
                self.source = '<string>'
        else:
            self.source = self.options.source

        # Drain file-like objects to get their contents
        try:
            read = grammar.read
        except AttributeError:
            pass
        else:
            grammar = read()

        assert isinstance(grammar, STRING_TYPE)
        self.grammar_source = grammar
        if self.options.use_bytes:
            if not isascii(grammar):
                raise ValueError("Grammar must be ascii only, when use_bytes=True")
            if sys.version_info[0] == 2 and self.options.use_bytes != 'force':
                raise NotImplementedError("`use_bytes=True` may have issues on python2."
                                          "Use `use_bytes='force'` to use it at your own risk.")

        cache_fn = None
        if self.options.cache:
            if self.options.parser != 'lalr':
                raise NotImplementedError("cache only works with parser='lalr' for now")
            if isinstance(self.options.cache, STRING_TYPE):
                cache_fn = self.options.cache
            else:
                if self.options.cache is not True:
                    raise ValueError("cache argument must be bool or str")
                unhashable = ('transformer', 'postlex', 'lexer_callbacks', 'edit_terminals')
                from . import __version__
                options_str = ''.join(k+str(v) for k, v in options.items() if k not in unhashable)
                s = grammar + options_str + __version__
                md5 = hashlib.md5(s.encode()).hexdigest()
                cache_fn = '.lark_cache_%s.tmp' % md5

            if FS.exists(cache_fn):
                logger.debug('Loading grammar from cache: %s', cache_fn)
                with FS.open(cache_fn, 'rb') as f:
                    self._load(f, self.options.transformer, self.options.postlex)
                return

        if self.options.lexer == 'auto':
            if self.options.parser == 'lalr':
                self.options.lexer = 'contextual'
            elif self.options.parser == 'earley':
                self.options.lexer = 'dynamic'
            elif self.options.parser == 'cyk':
                self.options.lexer = 'standard'
            else:
                assert False, self.options.parser
        lexer = self.options.lexer
        assert lexer in ('standard', 'contextual', 'dynamic', 'dynamic_complete') or issubclass(lexer, Lexer)

        if self.options.ambiguity == 'auto':
            if self.options.parser == 'earley':
                self.options.ambiguity = 'resolve'
        else:
            disambig_parsers = ['earley', 'cyk']
            assert self.options.parser in disambig_parsers, (
                'Only %s supports disambiguation right now') % ', '.join(disambig_parsers)

        if self.options.priority == 'auto':
            if self.options.parser in ('earley', 'cyk', ):
                self.options.priority = 'normal'
            elif self.options.parser in ('lalr', ):
                self.options.priority = None
        elif self.options.priority in ('invert', 'normal'):
            assert self.options.parser in ('earley', 'cyk'), "priorities are not supported for LALR at this time"

        assert self.options.priority in ('auto', None, 'normal', 'invert'), 'invalid priority option specified: {}. options are auto, none, normal, invert.'.format(self.options.priority)
        assert self.options.ambiguity not in ('resolve__antiscore_sum', ), 'resolve__antiscore_sum has been replaced with the option priority="invert"'
        assert self.options.ambiguity in ('resolve', 'explicit', 'forest', 'auto', )

        # Parse the grammar file and compose the grammars (TODO)
        self.grammar = load_grammar(grammar, self.source, re_module, self.options.import_sources)

        # Compile the EBNF grammar into BNF
        self.terminals, self.rules, self.ignore_tokens = self.grammar.compile(self.options.start)

        if self.options.edit_terminals:
            for t in self.terminals:
                self.options.edit_terminals(t)

        self._terminals_dict = {t.name: t for t in self.terminals}

        # If the user asked to invert the priorities, negate them all here.
        # This replaces the old 'resolve__antiscore_sum' option.
        if self.options.priority == 'invert':
            for rule in self.rules:
                if rule.options.priority is not None:
                    rule.options.priority = -rule.options.priority
        # Else, if the user asked to disable priorities, strip them from the
        # rules. This allows the Earley parsers to skip an extra forest walk
        # for improved performance, if you don't need them (or didn't specify any).
        elif self.options.priority == None:
            for rule in self.rules:
                if rule.options.priority is not None:
                    rule.options.priority = None

        # TODO Deprecate lexer_callbacks?
        lexer_callbacks = (_get_lexer_callbacks(self.options.transformer, self.terminals)
                           if self.options.transformer
                           else {})
        lexer_callbacks.update(self.options.lexer_callbacks)

        self.lexer_conf = LexerConf(self.terminals, re_module, self.ignore_tokens, self.options.postlex, lexer_callbacks, self.options.g_regex_flags, use_bytes=self.options.use_bytes)

        if self.options.parser:
            self.parser = self._build_parser()
        elif lexer:
            self.lexer = self._build_lexer()

        if cache_fn:
            logger.debug('Saving grammar to cache: %s', cache_fn)
            with FS.open(cache_fn, 'wb') as f:
                self.save(f)

    __doc__ += "\n\n" + LarkOptions.OPTIONS_DOC

    __serialize_fields__ = 'parser', 'rules', 'options'

    def _build_lexer(self):
        return TraditionalLexer(self.lexer_conf)

    def _prepare_callbacks(self):
        self.parser_class = get_frontend(self.options.parser, self.options.lexer)
        self._callbacks = None
        # we don't need these callbacks if we aren't building a tree
        if self.options.ambiguity != 'forest':
            self._parse_tree_builder = ParseTreeBuilder(self.rules, self.options.tree_class or Tree, self.options.propagate_positions, self.options.keep_all_tokens, self.options.parser!='lalr' and self.options.ambiguity=='explicit', self.options.maybe_placeholders)
            self._callbacks = self._parse_tree_builder.create_callback(self.options.transformer)

    def _build_parser(self):
        self._prepare_callbacks()
        parser_conf = ParserConf(self.rules, self._callbacks, self.options.start)
        return self.parser_class(self.lexer_conf, parser_conf, options=self.options)

    def save(self, f):
        """Saves the instance into the given file object

        Useful for caching and multiprocessing.
        """
        data, m = self.memo_serialize([TerminalDef, Rule])
        pickle.dump({'data': data, 'memo': m}, f)

    @classmethod
    def load(cls, f):
        """Loads an instance from the given file object

        Useful for caching and multiprocessing.
        """
        inst = cls.__new__(cls)
        return inst._load(f)

    def _load(self, f, transformer=None, postlex=None):
        if isinstance(f, dict):
            d = f
        else:
            d = pickle.load(f)
        memo = d['memo']
        data = d['data']

        assert memo
        memo = SerializeMemoizer.deserialize(memo, {'Rule': Rule, 'TerminalDef': TerminalDef}, {})
        options = dict(data['options'])
        if transformer is not None:
            options['transformer'] = transformer
        if postlex is not None:
            options['postlex'] = postlex
        self.options = LarkOptions.deserialize(options, memo)
        re_module = regex if self.options.regex else re
        self.rules = [Rule.deserialize(r, memo) for r in data['rules']]
        self.source = '<deserialized>'
        self._prepare_callbacks()
        self.parser = self.parser_class.deserialize(
            data['parser'],
            memo,
            self._callbacks,
            self.options.postlex,
            self.options.transformer,
            re_module
        )
        self.terminals = self.parser.lexer_conf.tokens
        self._terminals_dict = {t.name: t for t in self.terminals}
        return self

    @classmethod
    def _load_from_dict(cls, data, memo, transformer=None, postlex=None):
        inst = cls.__new__(cls)
        return inst._load({'data': data, 'memo': memo}, transformer, postlex)

    @classmethod
    def open(cls, grammar_filename, rel_to=None, **options):
        """Create an instance of Lark with the grammar given by its filename

        If ``rel_to`` is provided, the function will find the grammar filename in relation to it.

        Example:

            >>> Lark.open("grammar_file.lark", rel_to=__file__, parser="lalr")
            Lark(...)

        """
        if rel_to:
            basepath = os.path.dirname(rel_to)
            grammar_filename = os.path.join(basepath, grammar_filename)
        with open(grammar_filename, encoding='utf8') as f:
            return cls(f, **options)
    
    @classmethod
    def open_from_package(cls, package, grammar_path, search_paths=("",), **options):
        """Create an instance of Lark with the grammar loaded from within the package `package`.
        This allows grammar loading from zipapps.
        
        Will also create a `FromPackageLoader` instance and add it to the `import_sources` to simplify importing
        
        ``search_paths`` is passed to `FromPackageLoader`
        
        Example:
            
            Lark.open_from_package(__name__, "example.lark", ("grammars",), parser=...)
        """
        package = FromPackageLoader(package, search_paths)
        full_path, text = package([], grammar_path)
        options.setdefault('source', full_path)
        if 'import_sources' in options:
            options['import_sources'].append(package)
        else:
            options['import_sources'] = [package]
        return cls(text, **options)

    def __repr__(self):
        return 'Lark(open(%r), parser=%r, lexer=%r, ...)' % (self.source, self.options.parser, self.options.lexer)


    def lex(self, text):
        "Only lex (and postlex) the text, without parsing it. Only relevant when lexer='standard'"
        if not hasattr(self, 'lexer'):
            self.lexer = self._build_lexer()
        stream = self.lexer.lex(text)
        if self.options.postlex:
            return self.options.postlex.process(stream)
        return stream

    def get_terminal(self, name):
        "Get information about a terminal"
        return self._terminals_dict[name]

    def parse(self, text, start=None, on_error=None):
        """Parse the given text, according to the options provided.

        Parameters:
            text (str): Text to be parsed.
            start (str, optional): Required if Lark was given multiple possible start symbols (using the start option).
            on_error (function, optional): if provided, will be called on UnexpectedToken error. Return true to resume parsing.
                LALR only. See examples/error_puppet.py for an example of how to use on_error.

        Returns:
            If a transformer is supplied to ``__init__``, returns whatever is the
            result of the transformation. Otherwise, returns a Tree instance.

        """

        try:
            return self.parser.parse(text, start=start)
        except UnexpectedToken as e:
            if on_error is None:
                raise

            while True:
                if not on_error(e):
                    raise e
                try:
                    return e.puppet.resume_parse()
                except UnexpectedToken as e2:
                    if e.token.type == e2.token.type == '$END' and e.puppet == e2.puppet:
                        # Prevent infinite loop
                        raise e2
                    e = e2


###}
