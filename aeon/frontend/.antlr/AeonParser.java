// Generated from c:\Users\Paulo Santos\Desktop\git\aeon\aeonlang\aeon\frontend\Aeon.g4 by ANTLR 4.7.1
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class AeonParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.7.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		IMPORT=1, FROM=2, IF=3, ELSE=4, QUESTION=5, MAXIMIZE=6, MINIMIZE=7, EVALUATE=8, 
		PLUS=9, MINUS=10, MULT=11, QUOT=12, MODULE=13, POWER=14, CONJUNCTION=15, 
		DISJUNCTION=16, NOT=17, PIPE=18, LT=19, LE=20, GT=21, GE=22, EQUAL=23, 
		DIFF=24, ASSIGN=25, RARROW=26, FATARROW=27, IMPLIE=28, LBRACE=29, RBRACE=30, 
		LPARENS=31, RPARENS=32, LBRACKET=33, RBRACKET=34, TYPEE=35, AS=36, AND=37, 
		WHERE=38, NATIVE=39, UNINTERPRETED=40, ABSTRACTION=41, DOTDOT=42, DOT=43, 
		COLON=44, COMMA=45, SEMICOLON=46, BOOLEAN=47, INTEGER=48, FLOAT=49, STRING=50, 
		IDENTIFIER=51, TYPEE_IDENTIFIER=52, ABSTRACT_TYPEE_IDENTIFIER=53, LINE_COMMENT=54, 
		BLOCK_COMMENT=55, WS=56;
	public static final int
		RULE_aeon = 0, RULE_imprt = 1, RULE_regular_import = 2, RULE_function_import = 3, 
		RULE_import_path = 4, RULE_typee_alias = 5, RULE_typee_declaration = 6, 
		RULE_regular_typee_declaration = 7, RULE_parameterized_typee_declaration = 8, 
		RULE_parameters_typee_declaration = 9, RULE_typee = 10, RULE_typee_refined = 11, 
		RULE_typee_abstraction_type = 12, RULE_typee_definition = 13, RULE_typee_basic_type = 14, 
		RULE_typee_type_abstract = 15, RULE_typee_abstract_parameters = 16, RULE_function = 17, 
		RULE_function_identifier = 18, RULE_function_parameters = 19, RULE_function_where = 20, 
		RULE_function_body = 21, RULE_statement = 22, RULE_variable_definition = 23, 
		RULE_variable_assignment = 24, RULE_if_statement = 25, RULE_expression = 26, 
		RULE_function_abstraction = 27, RULE_call_parameters = 28;
	public static final String[] ruleNames = {
		"aeon", "imprt", "regular_import", "function_import", "import_path", "typee_alias", 
		"typee_declaration", "regular_typee_declaration", "parameterized_typee_declaration", 
		"parameters_typee_declaration", "typee", "typee_refined", "typee_abstraction_type", 
		"typee_definition", "typee_basic_type", "typee_type_abstract", "typee_abstract_parameters", 
		"function", "function_identifier", "function_parameters", "function_where", 
		"function_body", "statement", "variable_definition", "variable_assignment", 
		"if_statement", "expression", "function_abstraction", "call_parameters"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'import'", "'from'", "'if'", "'else'", "'?'", "'@maximize'", "'@minimize'", 
		"'@evaluate'", "'+'", "'-'", "'*'", "'/'", "'%'", "'^'", "'&&'", "'||'", 
		"'!'", "'|'", "'<'", "'<='", "'>'", "'>='", "'=='", "'!='", "'='", "'->'", 
		"'=>'", "'-->'", "'{'", "'}'", "'('", "')'", "'['", "']'", "'type'", "'as'", 
		"'and'", "'where'", "'native'", "'uninterpreted'", "'\\'", "'..'", "'.'", 
		"':'", "','", "';'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "IMPORT", "FROM", "IF", "ELSE", "QUESTION", "MAXIMIZE", "MINIMIZE", 
		"EVALUATE", "PLUS", "MINUS", "MULT", "QUOT", "MODULE", "POWER", "CONJUNCTION", 
		"DISJUNCTION", "NOT", "PIPE", "LT", "LE", "GT", "GE", "EQUAL", "DIFF", 
		"ASSIGN", "RARROW", "FATARROW", "IMPLIE", "LBRACE", "RBRACE", "LPARENS", 
		"RPARENS", "LBRACKET", "RBRACKET", "TYPEE", "AS", "AND", "WHERE", "NATIVE", 
		"UNINTERPRETED", "ABSTRACTION", "DOTDOT", "DOT", "COLON", "COMMA", "SEMICOLON", 
		"BOOLEAN", "INTEGER", "FLOAT", "STRING", "IDENTIFIER", "TYPEE_IDENTIFIER", 
		"ABSTRACT_TYPEE_IDENTIFIER", "LINE_COMMENT", "BLOCK_COMMENT", "WS"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Aeon.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public AeonParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class AeonContext extends ParserRuleContext {
		public TerminalNode EOF() { return getToken(AeonParser.EOF, 0); }
		public List<ImprtContext> imprt() {
			return getRuleContexts(ImprtContext.class);
		}
		public ImprtContext imprt(int i) {
			return getRuleContext(ImprtContext.class,i);
		}
		public List<Typee_aliasContext> typee_alias() {
			return getRuleContexts(Typee_aliasContext.class);
		}
		public Typee_aliasContext typee_alias(int i) {
			return getRuleContext(Typee_aliasContext.class,i);
		}
		public List<Typee_declarationContext> typee_declaration() {
			return getRuleContexts(Typee_declarationContext.class);
		}
		public Typee_declarationContext typee_declaration(int i) {
			return getRuleContext(Typee_declarationContext.class,i);
		}
		public List<FunctionContext> function() {
			return getRuleContexts(FunctionContext.class);
		}
		public FunctionContext function(int i) {
			return getRuleContext(FunctionContext.class,i);
		}
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public List<TypeeContext> typee() {
			return getRuleContexts(TypeeContext.class);
		}
		public TypeeContext typee(int i) {
			return getRuleContext(TypeeContext.class,i);
		}
		public AeonContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_aeon; }
	}

	public final AeonContext aeon() throws RecognitionException {
		AeonContext _localctx = new AeonContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_aeon);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(66);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << IMPORT) | (1L << IF) | (1L << QUESTION) | (1L << MAXIMIZE) | (1L << MINIMIZE) | (1L << EVALUATE) | (1L << MINUS) | (1L << NOT) | (1L << LBRACE) | (1L << LPARENS) | (1L << TYPEE) | (1L << ABSTRACTION) | (1L << BOOLEAN) | (1L << INTEGER) | (1L << FLOAT) | (1L << STRING) | (1L << IDENTIFIER) | (1L << TYPEE_IDENTIFIER) | (1L << ABSTRACT_TYPEE_IDENTIFIER))) != 0)) {
				{
				setState(64);
				_errHandler.sync(this);
				switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
				case 1:
					{
					setState(58);
					imprt();
					}
					break;
				case 2:
					{
					setState(59);
					typee_alias();
					}
					break;
				case 3:
					{
					setState(60);
					typee_declaration();
					}
					break;
				case 4:
					{
					setState(61);
					function();
					}
					break;
				case 5:
					{
					setState(62);
					statement();
					}
					break;
				case 6:
					{
					setState(63);
					typee();
					}
					break;
				}
				}
				setState(68);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(69);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ImprtContext extends ParserRuleContext {
		public Regular_importContext regular_import() {
			return getRuleContext(Regular_importContext.class,0);
		}
		public Function_importContext function_import() {
			return getRuleContext(Function_importContext.class,0);
		}
		public ImprtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_imprt; }
	}

	public final ImprtContext imprt() throws RecognitionException {
		ImprtContext _localctx = new ImprtContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_imprt);
		try {
			setState(73);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(71);
				regular_import();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(72);
				function_import();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Regular_importContext extends ParserRuleContext {
		public Import_pathContext path;
		public TerminalNode IMPORT() { return getToken(AeonParser.IMPORT, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public Import_pathContext import_path() {
			return getRuleContext(Import_pathContext.class,0);
		}
		public Regular_importContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_regular_import; }
	}

	public final Regular_importContext regular_import() throws RecognitionException {
		Regular_importContext _localctx = new Regular_importContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_regular_import);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(75);
			match(IMPORT);
			setState(76);
			((Regular_importContext)_localctx).path = import_path();
			setState(77);
			match(SEMICOLON);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Function_importContext extends ParserRuleContext {
		public Token functionName;
		public Import_pathContext path;
		public TerminalNode IMPORT() { return getToken(AeonParser.IMPORT, 0); }
		public TerminalNode FROM() { return getToken(AeonParser.FROM, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public TerminalNode IDENTIFIER() { return getToken(AeonParser.IDENTIFIER, 0); }
		public Import_pathContext import_path() {
			return getRuleContext(Import_pathContext.class,0);
		}
		public Function_importContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_import; }
	}

	public final Function_importContext function_import() throws RecognitionException {
		Function_importContext _localctx = new Function_importContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_function_import);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(79);
			match(IMPORT);
			setState(80);
			((Function_importContext)_localctx).functionName = match(IDENTIFIER);
			setState(81);
			match(FROM);
			setState(82);
			((Function_importContext)_localctx).path = import_path();
			setState(83);
			match(SEMICOLON);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Import_pathContext extends ParserRuleContext {
		public Token directory;
		public Token name;
		public List<TerminalNode> IDENTIFIER() { return getTokens(AeonParser.IDENTIFIER); }
		public TerminalNode IDENTIFIER(int i) {
			return getToken(AeonParser.IDENTIFIER, i);
		}
		public List<TerminalNode> QUOT() { return getTokens(AeonParser.QUOT); }
		public TerminalNode QUOT(int i) {
			return getToken(AeonParser.QUOT, i);
		}
		public List<TerminalNode> DOTDOT() { return getTokens(AeonParser.DOTDOT); }
		public TerminalNode DOTDOT(int i) {
			return getToken(AeonParser.DOTDOT, i);
		}
		public Import_pathContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_import_path; }
	}

	public final Import_pathContext import_path() throws RecognitionException {
		Import_pathContext _localctx = new Import_pathContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_import_path);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(89);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(85);
					((Import_pathContext)_localctx).directory = _input.LT(1);
					_la = _input.LA(1);
					if ( !(_la==DOTDOT || _la==IDENTIFIER) ) {
						((Import_pathContext)_localctx).directory = (Token)_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					setState(86);
					match(QUOT);
					}
					} 
				}
				setState(91);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			}
			setState(92);
			((Import_pathContext)_localctx).name = match(IDENTIFIER);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_aliasContext extends ParserRuleContext {
		public Typee_basic_typeContext name;
		public TypeeContext alias;
		public TerminalNode TYPEE() { return getToken(AeonParser.TYPEE, 0); }
		public TerminalNode AS() { return getToken(AeonParser.AS, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public Typee_basic_typeContext typee_basic_type() {
			return getRuleContext(Typee_basic_typeContext.class,0);
		}
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public Typee_aliasContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_alias; }
	}

	public final Typee_aliasContext typee_alias() throws RecognitionException {
		Typee_aliasContext _localctx = new Typee_aliasContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_typee_alias);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(94);
			match(TYPEE);
			setState(95);
			((Typee_aliasContext)_localctx).name = typee_basic_type();
			setState(96);
			match(AS);
			setState(97);
			((Typee_aliasContext)_localctx).alias = typee();
			setState(98);
			match(SEMICOLON);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_declarationContext extends ParserRuleContext {
		public Regular_typee_declarationContext regular_typee_declaration() {
			return getRuleContext(Regular_typee_declarationContext.class,0);
		}
		public Parameterized_typee_declarationContext parameterized_typee_declaration() {
			return getRuleContext(Parameterized_typee_declarationContext.class,0);
		}
		public Typee_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_declaration; }
	}

	public final Typee_declarationContext typee_declaration() throws RecognitionException {
		Typee_declarationContext _localctx = new Typee_declarationContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_typee_declaration);
		try {
			setState(102);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(100);
				regular_typee_declaration();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(101);
				parameterized_typee_declaration();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Regular_typee_declarationContext extends ParserRuleContext {
		public TypeeContext name;
		public TerminalNode TYPEE() { return getToken(AeonParser.TYPEE, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public Regular_typee_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_regular_typee_declaration; }
	}

	public final Regular_typee_declarationContext regular_typee_declaration() throws RecognitionException {
		Regular_typee_declarationContext _localctx = new Regular_typee_declarationContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_regular_typee_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(104);
			match(TYPEE);
			setState(105);
			((Regular_typee_declarationContext)_localctx).name = typee();
			setState(106);
			match(SEMICOLON);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Parameterized_typee_declarationContext extends ParserRuleContext {
		public TypeeContext name;
		public Parameters_typee_declarationContext params;
		public TerminalNode TYPEE() { return getToken(AeonParser.TYPEE, 0); }
		public TerminalNode LBRACE() { return getToken(AeonParser.LBRACE, 0); }
		public TerminalNode RBRACE() { return getToken(AeonParser.RBRACE, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public Parameters_typee_declarationContext parameters_typee_declaration() {
			return getRuleContext(Parameters_typee_declarationContext.class,0);
		}
		public Parameterized_typee_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_parameterized_typee_declaration; }
	}

	public final Parameterized_typee_declarationContext parameterized_typee_declaration() throws RecognitionException {
		Parameterized_typee_declarationContext _localctx = new Parameterized_typee_declarationContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_parameterized_typee_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(108);
			match(TYPEE);
			setState(109);
			((Parameterized_typee_declarationContext)_localctx).name = typee();
			setState(110);
			match(LBRACE);
			setState(111);
			((Parameterized_typee_declarationContext)_localctx).params = parameters_typee_declaration();
			setState(112);
			match(RBRACE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Parameters_typee_declarationContext extends ParserRuleContext {
		public List<Typee_definitionContext> typee_definition() {
			return getRuleContexts(Typee_definitionContext.class);
		}
		public Typee_definitionContext typee_definition(int i) {
			return getRuleContext(Typee_definitionContext.class,i);
		}
		public List<TerminalNode> SEMICOLON() { return getTokens(AeonParser.SEMICOLON); }
		public TerminalNode SEMICOLON(int i) {
			return getToken(AeonParser.SEMICOLON, i);
		}
		public Parameters_typee_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_parameters_typee_declaration; }
	}

	public final Parameters_typee_declarationContext parameters_typee_declaration() throws RecognitionException {
		Parameters_typee_declarationContext _localctx = new Parameters_typee_declarationContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_parameters_typee_declaration);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(117); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(114);
				typee_definition();
				setState(115);
				match(SEMICOLON);
				}
				}
				setState(119); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==IDENTIFIER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeeContext extends ParserRuleContext {
		public Typee_refinedContext typee_refined() {
			return getRuleContext(Typee_refinedContext.class,0);
		}
		public Typee_abstraction_typeContext typee_abstraction_type() {
			return getRuleContext(Typee_abstraction_typeContext.class,0);
		}
		public Typee_definitionContext typee_definition() {
			return getRuleContext(Typee_definitionContext.class,0);
		}
		public Typee_basic_typeContext typee_basic_type() {
			return getRuleContext(Typee_basic_typeContext.class,0);
		}
		public Typee_type_abstractContext typee_type_abstract() {
			return getRuleContext(Typee_type_abstractContext.class,0);
		}
		public TypeeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee; }
	}

	public final TypeeContext typee() throws RecognitionException {
		TypeeContext _localctx = new TypeeContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_typee);
		try {
			setState(126);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(121);
				typee_refined();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(122);
				typee_abstraction_type();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(123);
				typee_definition();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(124);
				typee_basic_type();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(125);
				typee_type_abstract();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_refinedContext extends ParserRuleContext {
		public TypeeContext typeeRefined;
		public ExpressionContext condition;
		public TerminalNode LBRACE() { return getToken(AeonParser.LBRACE, 0); }
		public TerminalNode PIPE() { return getToken(AeonParser.PIPE, 0); }
		public TerminalNode RBRACE() { return getToken(AeonParser.RBRACE, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public Typee_refinedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_refined; }
	}

	public final Typee_refinedContext typee_refined() throws RecognitionException {
		Typee_refinedContext _localctx = new Typee_refinedContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_typee_refined);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(128);
			match(LBRACE);
			setState(129);
			((Typee_refinedContext)_localctx).typeeRefined = typee();
			setState(130);
			match(PIPE);
			setState(131);
			((Typee_refinedContext)_localctx).condition = expression(0);
			setState(132);
			match(RBRACE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_abstraction_typeContext extends ParserRuleContext {
		public TypeeContext argTypee;
		public TypeeContext returnTypee;
		public TerminalNode LPARENS() { return getToken(AeonParser.LPARENS, 0); }
		public TerminalNode RARROW() { return getToken(AeonParser.RARROW, 0); }
		public TerminalNode RPARENS() { return getToken(AeonParser.RPARENS, 0); }
		public List<TypeeContext> typee() {
			return getRuleContexts(TypeeContext.class);
		}
		public TypeeContext typee(int i) {
			return getRuleContext(TypeeContext.class,i);
		}
		public Typee_abstraction_typeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_abstraction_type; }
	}

	public final Typee_abstraction_typeContext typee_abstraction_type() throws RecognitionException {
		Typee_abstraction_typeContext _localctx = new Typee_abstraction_typeContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_typee_abstraction_type);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(134);
			match(LPARENS);
			setState(135);
			((Typee_abstraction_typeContext)_localctx).argTypee = typee();
			setState(136);
			match(RARROW);
			setState(137);
			((Typee_abstraction_typeContext)_localctx).returnTypee = typee();
			setState(138);
			match(RPARENS);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_definitionContext extends ParserRuleContext {
		public Token varName;
		public TypeeContext varTypee;
		public TerminalNode COLON() { return getToken(AeonParser.COLON, 0); }
		public TerminalNode IDENTIFIER() { return getToken(AeonParser.IDENTIFIER, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public Typee_definitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_definition; }
	}

	public final Typee_definitionContext typee_definition() throws RecognitionException {
		Typee_definitionContext _localctx = new Typee_definitionContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_typee_definition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(140);
			((Typee_definitionContext)_localctx).varName = match(IDENTIFIER);
			setState(141);
			match(COLON);
			setState(142);
			((Typee_definitionContext)_localctx).varTypee = typee();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_basic_typeContext extends ParserRuleContext {
		public Token basicType;
		public TerminalNode TYPEE_IDENTIFIER() { return getToken(AeonParser.TYPEE_IDENTIFIER, 0); }
		public TerminalNode ABSTRACT_TYPEE_IDENTIFIER() { return getToken(AeonParser.ABSTRACT_TYPEE_IDENTIFIER, 0); }
		public Typee_basic_typeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_basic_type; }
	}

	public final Typee_basic_typeContext typee_basic_type() throws RecognitionException {
		Typee_basic_typeContext _localctx = new Typee_basic_typeContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_typee_basic_type);
		try {
			setState(146);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case TYPEE_IDENTIFIER:
				enterOuterAlt(_localctx, 1);
				{
				setState(144);
				((Typee_basic_typeContext)_localctx).basicType = match(TYPEE_IDENTIFIER);
				}
				break;
			case ABSTRACT_TYPEE_IDENTIFIER:
				enterOuterAlt(_localctx, 2);
				{
				setState(145);
				((Typee_basic_typeContext)_localctx).basicType = match(ABSTRACT_TYPEE_IDENTIFIER);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_type_abstractContext extends ParserRuleContext {
		public Token abstractType;
		public Typee_abstract_parametersContext abstractParams;
		public TerminalNode LBRACKET() { return getToken(AeonParser.LBRACKET, 0); }
		public TerminalNode RBRACKET() { return getToken(AeonParser.RBRACKET, 0); }
		public TerminalNode TYPEE_IDENTIFIER() { return getToken(AeonParser.TYPEE_IDENTIFIER, 0); }
		public Typee_abstract_parametersContext typee_abstract_parameters() {
			return getRuleContext(Typee_abstract_parametersContext.class,0);
		}
		public Typee_type_abstractContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_type_abstract; }
	}

	public final Typee_type_abstractContext typee_type_abstract() throws RecognitionException {
		Typee_type_abstractContext _localctx = new Typee_type_abstractContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_typee_type_abstract);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(148);
			((Typee_type_abstractContext)_localctx).abstractType = match(TYPEE_IDENTIFIER);
			setState(149);
			match(LBRACKET);
			setState(150);
			((Typee_type_abstractContext)_localctx).abstractParams = typee_abstract_parameters();
			setState(151);
			match(RBRACKET);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typee_abstract_parametersContext extends ParserRuleContext {
		public TypeeContext abstractParam;
		public TypeeContext restAbstractParams;
		public List<TypeeContext> typee() {
			return getRuleContexts(TypeeContext.class);
		}
		public TypeeContext typee(int i) {
			return getRuleContext(TypeeContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(AeonParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(AeonParser.COMMA, i);
		}
		public Typee_abstract_parametersContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typee_abstract_parameters; }
	}

	public final Typee_abstract_parametersContext typee_abstract_parameters() throws RecognitionException {
		Typee_abstract_parametersContext _localctx = new Typee_abstract_parametersContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_typee_abstract_parameters);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(153);
			((Typee_abstract_parametersContext)_localctx).abstractParam = typee();
			setState(158);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(154);
				match(COMMA);
				setState(155);
				((Typee_abstract_parametersContext)_localctx).restAbstractParams = typee();
				}
				}
				setState(160);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionContext extends ParserRuleContext {
		public Function_identifierContext name;
		public Function_parametersContext params;
		public TypeeContext returnType;
		public Function_whereContext where;
		public Function_bodyContext body;
		public TerminalNode LPARENS() { return getToken(AeonParser.LPARENS, 0); }
		public TerminalNode RPARENS() { return getToken(AeonParser.RPARENS, 0); }
		public TerminalNode RARROW() { return getToken(AeonParser.RARROW, 0); }
		public Function_identifierContext function_identifier() {
			return getRuleContext(Function_identifierContext.class,0);
		}
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public Function_bodyContext function_body() {
			return getRuleContext(Function_bodyContext.class,0);
		}
		public Function_parametersContext function_parameters() {
			return getRuleContext(Function_parametersContext.class,0);
		}
		public Function_whereContext function_where() {
			return getRuleContext(Function_whereContext.class,0);
		}
		public FunctionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function; }
	}

	public final FunctionContext function() throws RecognitionException {
		FunctionContext _localctx = new FunctionContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_function);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(161);
			((FunctionContext)_localctx).name = function_identifier();
			setState(162);
			match(LPARENS);
			setState(164);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << LBRACE) | (1L << LPARENS) | (1L << IDENTIFIER) | (1L << TYPEE_IDENTIFIER) | (1L << ABSTRACT_TYPEE_IDENTIFIER))) != 0)) {
				{
				setState(163);
				((FunctionContext)_localctx).params = function_parameters();
				}
			}

			setState(166);
			match(RPARENS);
			setState(167);
			match(RARROW);
			setState(168);
			((FunctionContext)_localctx).returnType = typee();
			setState(170);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==WHERE) {
				{
				setState(169);
				((FunctionContext)_localctx).where = function_where();
				}
			}

			setState(172);
			((FunctionContext)_localctx).body = function_body();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Function_identifierContext extends ParserRuleContext {
		public Token name;
		public Typee_abstract_parametersContext abstractParams;
		public TerminalNode IDENTIFIER() { return getToken(AeonParser.IDENTIFIER, 0); }
		public TerminalNode LBRACKET() { return getToken(AeonParser.LBRACKET, 0); }
		public TerminalNode RBRACKET() { return getToken(AeonParser.RBRACKET, 0); }
		public Typee_abstract_parametersContext typee_abstract_parameters() {
			return getRuleContext(Typee_abstract_parametersContext.class,0);
		}
		public Function_identifierContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_identifier; }
	}

	public final Function_identifierContext function_identifier() throws RecognitionException {
		Function_identifierContext _localctx = new Function_identifierContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_function_identifier);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(174);
			((Function_identifierContext)_localctx).name = match(IDENTIFIER);
			setState(179);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==LBRACKET) {
				{
				setState(175);
				match(LBRACKET);
				setState(176);
				((Function_identifierContext)_localctx).abstractParams = typee_abstract_parameters();
				setState(177);
				match(RBRACKET);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Function_parametersContext extends ParserRuleContext {
		public List<TypeeContext> typee() {
			return getRuleContexts(TypeeContext.class);
		}
		public TypeeContext typee(int i) {
			return getRuleContext(TypeeContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(AeonParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(AeonParser.COMMA, i);
		}
		public Function_parametersContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_parameters; }
	}

	public final Function_parametersContext function_parameters() throws RecognitionException {
		Function_parametersContext _localctx = new Function_parametersContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_function_parameters);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(181);
			typee();
			setState(186);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(182);
				match(COMMA);
				setState(183);
				typee();
				}
				}
				setState(188);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Function_whereContext extends ParserRuleContext {
		public TerminalNode WHERE() { return getToken(AeonParser.WHERE, 0); }
		public TerminalNode LBRACE() { return getToken(AeonParser.LBRACE, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode RBRACE() { return getToken(AeonParser.RBRACE, 0); }
		public List<TerminalNode> AND() { return getTokens(AeonParser.AND); }
		public TerminalNode AND(int i) {
			return getToken(AeonParser.AND, i);
		}
		public Function_whereContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_where; }
	}

	public final Function_whereContext function_where() throws RecognitionException {
		Function_whereContext _localctx = new Function_whereContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_function_where);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(189);
			match(WHERE);
			setState(190);
			match(LBRACE);
			setState(191);
			expression(0);
			setState(196);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==AND) {
				{
				{
				setState(192);
				match(AND);
				setState(193);
				expression(0);
				}
				}
				setState(198);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(199);
			match(RBRACE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Function_bodyContext extends ParserRuleContext {
		public Function_bodyContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_body; }
	 
		public Function_bodyContext() { }
		public void copyFrom(Function_bodyContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class RegularBodyContext extends Function_bodyContext {
		public TerminalNode LBRACE() { return getToken(AeonParser.LBRACE, 0); }
		public TerminalNode RBRACE() { return getToken(AeonParser.RBRACE, 0); }
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public List<TerminalNode> SEMICOLON() { return getTokens(AeonParser.SEMICOLON); }
		public TerminalNode SEMICOLON(int i) {
			return getToken(AeonParser.SEMICOLON, i);
		}
		public RegularBodyContext(Function_bodyContext ctx) { copyFrom(ctx); }
	}
	public static class NativeBodyContext extends Function_bodyContext {
		public Token nativee;
		public TerminalNode ASSIGN() { return getToken(AeonParser.ASSIGN, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public TerminalNode NATIVE() { return getToken(AeonParser.NATIVE, 0); }
		public NativeBodyContext(Function_bodyContext ctx) { copyFrom(ctx); }
	}
	public static class UninterpretedBodyContext extends Function_bodyContext {
		public Token uninterpreted;
		public TerminalNode ASSIGN() { return getToken(AeonParser.ASSIGN, 0); }
		public TerminalNode SEMICOLON() { return getToken(AeonParser.SEMICOLON, 0); }
		public TerminalNode UNINTERPRETED() { return getToken(AeonParser.UNINTERPRETED, 0); }
		public UninterpretedBodyContext(Function_bodyContext ctx) { copyFrom(ctx); }
	}

	public final Function_bodyContext function_body() throws RecognitionException {
		Function_bodyContext _localctx = new Function_bodyContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_function_body);
		int _la;
		try {
			setState(217);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				_localctx = new NativeBodyContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(201);
				match(ASSIGN);
				setState(202);
				((NativeBodyContext)_localctx).nativee = match(NATIVE);
				setState(203);
				match(SEMICOLON);
				}
				break;
			case 2:
				_localctx = new UninterpretedBodyContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(204);
				match(ASSIGN);
				setState(205);
				((UninterpretedBodyContext)_localctx).uninterpreted = match(UNINTERPRETED);
				setState(206);
				match(SEMICOLON);
				}
				break;
			case 3:
				_localctx = new RegularBodyContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(207);
				match(LBRACE);
				setState(213);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << IF) | (1L << QUESTION) | (1L << MAXIMIZE) | (1L << MINIMIZE) | (1L << EVALUATE) | (1L << MINUS) | (1L << NOT) | (1L << LBRACE) | (1L << LPARENS) | (1L << ABSTRACTION) | (1L << BOOLEAN) | (1L << INTEGER) | (1L << FLOAT) | (1L << STRING) | (1L << IDENTIFIER) | (1L << TYPEE_IDENTIFIER) | (1L << ABSTRACT_TYPEE_IDENTIFIER))) != 0)) {
					{
					{
					setState(208);
					statement();
					setState(209);
					match(SEMICOLON);
					}
					}
					setState(215);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(216);
				match(RBRACE);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementContext extends ParserRuleContext {
		public Variable_definitionContext variable_definition() {
			return getRuleContext(Variable_definitionContext.class,0);
		}
		public Variable_assignmentContext variable_assignment() {
			return getRuleContext(Variable_assignmentContext.class,0);
		}
		public If_statementContext if_statement() {
			return getRuleContext(If_statementContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public StatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statement; }
	}

	public final StatementContext statement() throws RecognitionException {
		StatementContext _localctx = new StatementContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_statement);
		try {
			setState(223);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(219);
				variable_definition();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(220);
				variable_assignment();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(221);
				if_statement();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(222);
				expression(0);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Variable_definitionContext extends ParserRuleContext {
		public TypeeContext variable;
		public ExpressionContext exp;
		public TerminalNode ASSIGN() { return getToken(AeonParser.ASSIGN, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public Variable_definitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variable_definition; }
	}

	public final Variable_definitionContext variable_definition() throws RecognitionException {
		Variable_definitionContext _localctx = new Variable_definitionContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_variable_definition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(225);
			((Variable_definitionContext)_localctx).variable = typee();
			setState(226);
			match(ASSIGN);
			setState(227);
			((Variable_definitionContext)_localctx).exp = expression(0);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Variable_assignmentContext extends ParserRuleContext {
		public Token variable;
		public ExpressionContext exp;
		public TerminalNode ASSIGN() { return getToken(AeonParser.ASSIGN, 0); }
		public TerminalNode IDENTIFIER() { return getToken(AeonParser.IDENTIFIER, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public Variable_assignmentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variable_assignment; }
	}

	public final Variable_assignmentContext variable_assignment() throws RecognitionException {
		Variable_assignmentContext _localctx = new Variable_assignmentContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_variable_assignment);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(229);
			((Variable_assignmentContext)_localctx).variable = match(IDENTIFIER);
			setState(230);
			match(ASSIGN);
			setState(231);
			((Variable_assignmentContext)_localctx).exp = expression(0);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class If_statementContext extends ParserRuleContext {
		public ExpressionContext cond;
		public Function_bodyContext then;
		public Function_bodyContext otherwise;
		public TerminalNode IF() { return getToken(AeonParser.IF, 0); }
		public TerminalNode ELSE() { return getToken(AeonParser.ELSE, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<Function_bodyContext> function_body() {
			return getRuleContexts(Function_bodyContext.class);
		}
		public Function_bodyContext function_body(int i) {
			return getRuleContext(Function_bodyContext.class,i);
		}
		public If_statementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_if_statement; }
	}

	public final If_statementContext if_statement() throws RecognitionException {
		If_statementContext _localctx = new If_statementContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_if_statement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(233);
			match(IF);
			setState(234);
			((If_statementContext)_localctx).cond = expression(0);
			setState(235);
			((If_statementContext)_localctx).then = function_body();
			setState(236);
			match(ELSE);
			setState(237);
			((If_statementContext)_localctx).otherwise = function_body();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionContext extends ParserRuleContext {
		public ExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expression; }
	 
		public ExpressionContext() { }
		public void copyFrom(ExpressionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class FitnessImprovementContext extends ExpressionContext {
		public Token improvement;
		public ExpressionContext param;
		public TerminalNode LPARENS() { return getToken(AeonParser.LPARENS, 0); }
		public TerminalNode RPARENS() { return getToken(AeonParser.RPARENS, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode MAXIMIZE() { return getToken(AeonParser.MAXIMIZE, 0); }
		public TerminalNode MINIMIZE() { return getToken(AeonParser.MINIMIZE, 0); }
		public TerminalNode EVALUATE() { return getToken(AeonParser.EVALUATE, 0); }
		public FitnessImprovementContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class LogicalExpressionContext extends ExpressionContext {
		public ExpressionContext left;
		public Token op;
		public ExpressionContext right;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode LT() { return getToken(AeonParser.LT, 0); }
		public TerminalNode LE() { return getToken(AeonParser.LE, 0); }
		public TerminalNode GT() { return getToken(AeonParser.GT, 0); }
		public TerminalNode GE() { return getToken(AeonParser.GE, 0); }
		public TerminalNode EQUAL() { return getToken(AeonParser.EQUAL, 0); }
		public TerminalNode DIFF() { return getToken(AeonParser.DIFF, 0); }
		public TerminalNode CONJUNCTION() { return getToken(AeonParser.CONJUNCTION, 0); }
		public TerminalNode DISJUNCTION() { return getToken(AeonParser.DISJUNCTION, 0); }
		public TerminalNode IMPLIE() { return getToken(AeonParser.IMPLIE, 0); }
		public LogicalExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class IfExpressionContext extends ExpressionContext {
		public ExpressionContext cond;
		public ExpressionContext then;
		public ExpressionContext otherwise;
		public TerminalNode QUESTION() { return getToken(AeonParser.QUESTION, 0); }
		public TerminalNode COLON() { return getToken(AeonParser.COLON, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public IfExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class ParenthesisContext extends ExpressionContext {
		public TerminalNode LPARENS() { return getToken(AeonParser.LPARENS, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode RPARENS() { return getToken(AeonParser.RPARENS, 0); }
		public ParenthesisContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class HoleContext extends ExpressionContext {
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public HoleContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class UnaryOperationContext extends ExpressionContext {
		public Token op;
		public ExpressionContext right;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode NOT() { return getToken(AeonParser.NOT, 0); }
		public TerminalNode MINUS() { return getToken(AeonParser.MINUS, 0); }
		public UnaryOperationContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class VariableContext extends ExpressionContext {
		public Token variable;
		public TerminalNode IDENTIFIER() { return getToken(AeonParser.IDENTIFIER, 0); }
		public VariableContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class AbstractionExpressionContext extends ExpressionContext {
		public TypeeContext variable;
		public ExpressionContext exp;
		public TerminalNode ABSTRACTION() { return getToken(AeonParser.ABSTRACTION, 0); }
		public TerminalNode RARROW() { return getToken(AeonParser.RARROW, 0); }
		public TypeeContext typee() {
			return getRuleContext(TypeeContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public AbstractionExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class LiteralContext extends ExpressionContext {
		public Token value;
		public TerminalNode INTEGER() { return getToken(AeonParser.INTEGER, 0); }
		public TerminalNode FLOAT() { return getToken(AeonParser.FLOAT, 0); }
		public TerminalNode BOOLEAN() { return getToken(AeonParser.BOOLEAN, 0); }
		public TerminalNode STRING() { return getToken(AeonParser.STRING, 0); }
		public LiteralContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class NumberExpressionContext extends ExpressionContext {
		public ExpressionContext left;
		public Token op;
		public ExpressionContext right;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode POWER() { return getToken(AeonParser.POWER, 0); }
		public TerminalNode MULT() { return getToken(AeonParser.MULT, 0); }
		public TerminalNode QUOT() { return getToken(AeonParser.QUOT, 0); }
		public TerminalNode MODULE() { return getToken(AeonParser.MODULE, 0); }
		public TerminalNode PLUS() { return getToken(AeonParser.PLUS, 0); }
		public TerminalNode MINUS() { return getToken(AeonParser.MINUS, 0); }
		public NumberExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class FunctionCallContext extends ExpressionContext {
		public ExpressionContext target;
		public Function_abstractionContext app;
		public Call_parametersContext params;
		public TerminalNode LPARENS() { return getToken(AeonParser.LPARENS, 0); }
		public TerminalNode RPARENS() { return getToken(AeonParser.RPARENS, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public Function_abstractionContext function_abstraction() {
			return getRuleContext(Function_abstractionContext.class,0);
		}
		public Call_parametersContext call_parameters() {
			return getRuleContext(Call_parametersContext.class,0);
		}
		public FunctionCallContext(ExpressionContext ctx) { copyFrom(ctx); }
	}
	public static class TypeeAttributeCallContext extends ExpressionContext {
		public Token variable;
		public Token attribute;
		public TerminalNode DOT() { return getToken(AeonParser.DOT, 0); }
		public List<TerminalNode> IDENTIFIER() { return getTokens(AeonParser.IDENTIFIER); }
		public TerminalNode IDENTIFIER(int i) {
			return getToken(AeonParser.IDENTIFIER, i);
		}
		public TypeeAttributeCallContext(ExpressionContext ctx) { copyFrom(ctx); }
	}

	public final ExpressionContext expression() throws RecognitionException {
		return expression(0);
	}

	private ExpressionContext expression(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ExpressionContext _localctx = new ExpressionContext(_ctx, _parentState);
		ExpressionContext _prevctx = _localctx;
		int _startState = 52;
		enterRecursionRule(_localctx, 52, RULE_expression, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(266);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
			case 1:
				{
				_localctx = new ParenthesisContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(240);
				match(LPARENS);
				setState(241);
				expression(0);
				setState(242);
				match(RPARENS);
				}
				break;
			case 2:
				{
				_localctx = new UnaryOperationContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(244);
				((UnaryOperationContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==MINUS || _la==NOT) ) {
					((UnaryOperationContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(245);
				((UnaryOperationContext)_localctx).right = expression(15);
				}
				break;
			case 3:
				{
				_localctx = new AbstractionExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(246);
				match(ABSTRACTION);
				setState(247);
				((AbstractionExpressionContext)_localctx).variable = typee();
				setState(248);
				match(RARROW);
				setState(249);
				((AbstractionExpressionContext)_localctx).exp = expression(7);
				}
				break;
			case 4:
				{
				_localctx = new TypeeAttributeCallContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(251);
				((TypeeAttributeCallContext)_localctx).variable = match(IDENTIFIER);
				setState(252);
				match(DOT);
				setState(253);
				((TypeeAttributeCallContext)_localctx).attribute = match(IDENTIFIER);
				}
				break;
			case 5:
				{
				_localctx = new HoleContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(254);
				match(QUESTION);
				setState(256);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << LBRACE) | (1L << LPARENS) | (1L << IDENTIFIER) | (1L << TYPEE_IDENTIFIER) | (1L << ABSTRACT_TYPEE_IDENTIFIER))) != 0)) {
					{
					setState(255);
					typee();
					}
				}

				setState(258);
				match(QUESTION);
				}
				break;
			case 6:
				{
				_localctx = new VariableContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(259);
				((VariableContext)_localctx).variable = match(IDENTIFIER);
				}
				break;
			case 7:
				{
				_localctx = new LiteralContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(260);
				((LiteralContext)_localctx).value = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << BOOLEAN) | (1L << INTEGER) | (1L << FLOAT) | (1L << STRING))) != 0)) ) {
					((LiteralContext)_localctx).value = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			case 8:
				{
				_localctx = new FitnessImprovementContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(261);
				((FitnessImprovementContext)_localctx).improvement = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << MAXIMIZE) | (1L << MINIMIZE) | (1L << EVALUATE))) != 0)) ) {
					((FitnessImprovementContext)_localctx).improvement = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(262);
				match(LPARENS);
				setState(263);
				((FitnessImprovementContext)_localctx).param = expression(0);
				setState(264);
				match(RPARENS);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(309);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,22,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(307);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,21,_ctx) ) {
					case 1:
						{
						_localctx = new NumberExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((NumberExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(268);
						if (!(precpred(_ctx, 16))) throw new FailedPredicateException(this, "precpred(_ctx, 16)");
						setState(269);
						((NumberExpressionContext)_localctx).op = match(POWER);
						setState(270);
						((NumberExpressionContext)_localctx).right = expression(17);
						}
						break;
					case 2:
						{
						_localctx = new NumberExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((NumberExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(271);
						if (!(precpred(_ctx, 14))) throw new FailedPredicateException(this, "precpred(_ctx, 14)");
						setState(272);
						((NumberExpressionContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << MULT) | (1L << QUOT) | (1L << MODULE) | (1L << POWER))) != 0)) ) {
							((NumberExpressionContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(273);
						((NumberExpressionContext)_localctx).right = expression(15);
						}
						break;
					case 3:
						{
						_localctx = new NumberExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((NumberExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(274);
						if (!(precpred(_ctx, 13))) throw new FailedPredicateException(this, "precpred(_ctx, 13)");
						setState(275);
						((NumberExpressionContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==PLUS || _la==MINUS) ) {
							((NumberExpressionContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(276);
						((NumberExpressionContext)_localctx).right = expression(14);
						}
						break;
					case 4:
						{
						_localctx = new LogicalExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((LogicalExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(277);
						if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
						setState(278);
						((LogicalExpressionContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << LT) | (1L << LE) | (1L << GT) | (1L << GE))) != 0)) ) {
							((LogicalExpressionContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(279);
						((LogicalExpressionContext)_localctx).right = expression(13);
						}
						break;
					case 5:
						{
						_localctx = new LogicalExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((LogicalExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(280);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(281);
						((LogicalExpressionContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==EQUAL || _la==DIFF) ) {
							((LogicalExpressionContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(282);
						((LogicalExpressionContext)_localctx).right = expression(12);
						}
						break;
					case 6:
						{
						_localctx = new LogicalExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((LogicalExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(283);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(284);
						((LogicalExpressionContext)_localctx).op = match(CONJUNCTION);
						setState(285);
						((LogicalExpressionContext)_localctx).right = expression(11);
						}
						break;
					case 7:
						{
						_localctx = new LogicalExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((LogicalExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(286);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(287);
						((LogicalExpressionContext)_localctx).op = match(DISJUNCTION);
						setState(288);
						((LogicalExpressionContext)_localctx).right = expression(10);
						}
						break;
					case 8:
						{
						_localctx = new LogicalExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((LogicalExpressionContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(289);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(290);
						((LogicalExpressionContext)_localctx).op = match(IMPLIE);
						setState(291);
						((LogicalExpressionContext)_localctx).right = expression(9);
						}
						break;
					case 9:
						{
						_localctx = new IfExpressionContext(new ExpressionContext(_parentctx, _parentState));
						((IfExpressionContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(292);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(293);
						match(QUESTION);
						setState(294);
						((IfExpressionContext)_localctx).then = expression(0);
						setState(295);
						match(COLON);
						setState(296);
						((IfExpressionContext)_localctx).otherwise = expression(7);
						}
						break;
					case 10:
						{
						_localctx = new FunctionCallContext(new ExpressionContext(_parentctx, _parentState));
						((FunctionCallContext)_localctx).target = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(298);
						if (!(precpred(_ctx, 17))) throw new FailedPredicateException(this, "precpred(_ctx, 17)");
						setState(300);
						_errHandler.sync(this);
						_la = _input.LA(1);
						if (_la==LBRACKET) {
							{
							setState(299);
							((FunctionCallContext)_localctx).app = function_abstraction();
							}
						}

						setState(302);
						match(LPARENS);
						setState(304);
						_errHandler.sync(this);
						_la = _input.LA(1);
						if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << QUESTION) | (1L << MAXIMIZE) | (1L << MINIMIZE) | (1L << EVALUATE) | (1L << MINUS) | (1L << NOT) | (1L << LPARENS) | (1L << ABSTRACTION) | (1L << BOOLEAN) | (1L << INTEGER) | (1L << FLOAT) | (1L << STRING) | (1L << IDENTIFIER))) != 0)) {
							{
							setState(303);
							((FunctionCallContext)_localctx).params = call_parameters();
							}
						}

						setState(306);
						match(RPARENS);
						}
						break;
					}
					} 
				}
				setState(311);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,22,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Function_abstractionContext extends ParserRuleContext {
		public TerminalNode LBRACKET() { return getToken(AeonParser.LBRACKET, 0); }
		public Typee_abstract_parametersContext typee_abstract_parameters() {
			return getRuleContext(Typee_abstract_parametersContext.class,0);
		}
		public TerminalNode RBRACKET() { return getToken(AeonParser.RBRACKET, 0); }
		public Function_abstractionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_function_abstraction; }
	}

	public final Function_abstractionContext function_abstraction() throws RecognitionException {
		Function_abstractionContext _localctx = new Function_abstractionContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_function_abstraction);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(312);
			match(LBRACKET);
			setState(313);
			typee_abstract_parameters();
			setState(314);
			match(RBRACKET);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Call_parametersContext extends ParserRuleContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(AeonParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(AeonParser.COMMA, i);
		}
		public Call_parametersContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_call_parameters; }
	}

	public final Call_parametersContext call_parameters() throws RecognitionException {
		Call_parametersContext _localctx = new Call_parametersContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_call_parameters);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(316);
			expression(0);
			setState(321);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(317);
				match(COMMA);
				setState(318);
				expression(0);
				}
				}
				setState(323);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 26:
			return expression_sempred((ExpressionContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean expression_sempred(ExpressionContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 16);
		case 1:
			return precpred(_ctx, 14);
		case 2:
			return precpred(_ctx, 13);
		case 3:
			return precpred(_ctx, 12);
		case 4:
			return precpred(_ctx, 11);
		case 5:
			return precpred(_ctx, 10);
		case 6:
			return precpred(_ctx, 9);
		case 7:
			return precpred(_ctx, 8);
		case 8:
			return precpred(_ctx, 6);
		case 9:
			return precpred(_ctx, 17);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3:\u0147\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\3\2\3\2\3\2\3\2\3\2"+
		"\3\2\7\2C\n\2\f\2\16\2F\13\2\3\2\3\2\3\3\3\3\5\3L\n\3\3\4\3\4\3\4\3\4"+
		"\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\7\6Z\n\6\f\6\16\6]\13\6\3\6\3\6\3\7\3"+
		"\7\3\7\3\7\3\7\3\7\3\b\3\b\5\bi\n\b\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3"+
		"\n\3\n\3\13\3\13\3\13\6\13x\n\13\r\13\16\13y\3\f\3\f\3\f\3\f\3\f\5\f\u0081"+
		"\n\f\3\r\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\16\3\16\3\17\3\17\3"+
		"\17\3\17\3\20\3\20\5\20\u0095\n\20\3\21\3\21\3\21\3\21\3\21\3\22\3\22"+
		"\3\22\7\22\u009f\n\22\f\22\16\22\u00a2\13\22\3\23\3\23\3\23\5\23\u00a7"+
		"\n\23\3\23\3\23\3\23\3\23\5\23\u00ad\n\23\3\23\3\23\3\24\3\24\3\24\3\24"+
		"\3\24\5\24\u00b6\n\24\3\25\3\25\3\25\7\25\u00bb\n\25\f\25\16\25\u00be"+
		"\13\25\3\26\3\26\3\26\3\26\3\26\7\26\u00c5\n\26\f\26\16\26\u00c8\13\26"+
		"\3\26\3\26\3\27\3\27\3\27\3\27\3\27\3\27\3\27\3\27\3\27\3\27\7\27\u00d6"+
		"\n\27\f\27\16\27\u00d9\13\27\3\27\5\27\u00dc\n\27\3\30\3\30\3\30\3\30"+
		"\5\30\u00e2\n\30\3\31\3\31\3\31\3\31\3\32\3\32\3\32\3\32\3\33\3\33\3\33"+
		"\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\34\3\34\3\34\3\34\5\34\u0103\n\34\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\34\5\34\u010d\n\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3\34\5\34\u012f\n\34\3\34"+
		"\3\34\5\34\u0133\n\34\3\34\7\34\u0136\n\34\f\34\16\34\u0139\13\34\3\35"+
		"\3\35\3\35\3\35\3\36\3\36\3\36\7\36\u0142\n\36\f\36\16\36\u0145\13\36"+
		"\3\36\2\3\66\37\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60\62"+
		"\64\668:\2\n\4\2,,\65\65\4\2\f\f\23\23\3\2\61\64\3\2\b\n\3\2\r\20\3\2"+
		"\13\f\3\2\25\30\3\2\31\32\2\u0159\2D\3\2\2\2\4K\3\2\2\2\6M\3\2\2\2\bQ"+
		"\3\2\2\2\n[\3\2\2\2\f`\3\2\2\2\16h\3\2\2\2\20j\3\2\2\2\22n\3\2\2\2\24"+
		"w\3\2\2\2\26\u0080\3\2\2\2\30\u0082\3\2\2\2\32\u0088\3\2\2\2\34\u008e"+
		"\3\2\2\2\36\u0094\3\2\2\2 \u0096\3\2\2\2\"\u009b\3\2\2\2$\u00a3\3\2\2"+
		"\2&\u00b0\3\2\2\2(\u00b7\3\2\2\2*\u00bf\3\2\2\2,\u00db\3\2\2\2.\u00e1"+
		"\3\2\2\2\60\u00e3\3\2\2\2\62\u00e7\3\2\2\2\64\u00eb\3\2\2\2\66\u010c\3"+
		"\2\2\28\u013a\3\2\2\2:\u013e\3\2\2\2<C\5\4\3\2=C\5\f\7\2>C\5\16\b\2?C"+
		"\5$\23\2@C\5.\30\2AC\5\26\f\2B<\3\2\2\2B=\3\2\2\2B>\3\2\2\2B?\3\2\2\2"+
		"B@\3\2\2\2BA\3\2\2\2CF\3\2\2\2DB\3\2\2\2DE\3\2\2\2EG\3\2\2\2FD\3\2\2\2"+
		"GH\7\2\2\3H\3\3\2\2\2IL\5\6\4\2JL\5\b\5\2KI\3\2\2\2KJ\3\2\2\2L\5\3\2\2"+
		"\2MN\7\3\2\2NO\5\n\6\2OP\7\60\2\2P\7\3\2\2\2QR\7\3\2\2RS\7\65\2\2ST\7"+
		"\4\2\2TU\5\n\6\2UV\7\60\2\2V\t\3\2\2\2WX\t\2\2\2XZ\7\16\2\2YW\3\2\2\2"+
		"Z]\3\2\2\2[Y\3\2\2\2[\\\3\2\2\2\\^\3\2\2\2][\3\2\2\2^_\7\65\2\2_\13\3"+
		"\2\2\2`a\7%\2\2ab\5\36\20\2bc\7&\2\2cd\5\26\f\2de\7\60\2\2e\r\3\2\2\2"+
		"fi\5\20\t\2gi\5\22\n\2hf\3\2\2\2hg\3\2\2\2i\17\3\2\2\2jk\7%\2\2kl\5\26"+
		"\f\2lm\7\60\2\2m\21\3\2\2\2no\7%\2\2op\5\26\f\2pq\7\37\2\2qr\5\24\13\2"+
		"rs\7 \2\2s\23\3\2\2\2tu\5\34\17\2uv\7\60\2\2vx\3\2\2\2wt\3\2\2\2xy\3\2"+
		"\2\2yw\3\2\2\2yz\3\2\2\2z\25\3\2\2\2{\u0081\5\30\r\2|\u0081\5\32\16\2"+
		"}\u0081\5\34\17\2~\u0081\5\36\20\2\177\u0081\5 \21\2\u0080{\3\2\2\2\u0080"+
		"|\3\2\2\2\u0080}\3\2\2\2\u0080~\3\2\2\2\u0080\177\3\2\2\2\u0081\27\3\2"+
		"\2\2\u0082\u0083\7\37\2\2\u0083\u0084\5\26\f\2\u0084\u0085\7\24\2\2\u0085"+
		"\u0086\5\66\34\2\u0086\u0087\7 \2\2\u0087\31\3\2\2\2\u0088\u0089\7!\2"+
		"\2\u0089\u008a\5\26\f\2\u008a\u008b\7\34\2\2\u008b\u008c\5\26\f\2\u008c"+
		"\u008d\7\"\2\2\u008d\33\3\2\2\2\u008e\u008f\7\65\2\2\u008f\u0090\7.\2"+
		"\2\u0090\u0091\5\26\f\2\u0091\35\3\2\2\2\u0092\u0095\7\66\2\2\u0093\u0095"+
		"\7\67\2\2\u0094\u0092\3\2\2\2\u0094\u0093\3\2\2\2\u0095\37\3\2\2\2\u0096"+
		"\u0097\7\66\2\2\u0097\u0098\7#\2\2\u0098\u0099\5\"\22\2\u0099\u009a\7"+
		"$\2\2\u009a!\3\2\2\2\u009b\u00a0\5\26\f\2\u009c\u009d\7/\2\2\u009d\u009f"+
		"\5\26\f\2\u009e\u009c\3\2\2\2\u009f\u00a2\3\2\2\2\u00a0\u009e\3\2\2\2"+
		"\u00a0\u00a1\3\2\2\2\u00a1#\3\2\2\2\u00a2\u00a0\3\2\2\2\u00a3\u00a4\5"+
		"&\24\2\u00a4\u00a6\7!\2\2\u00a5\u00a7\5(\25\2\u00a6\u00a5\3\2\2\2\u00a6"+
		"\u00a7\3\2\2\2\u00a7\u00a8\3\2\2\2\u00a8\u00a9\7\"\2\2\u00a9\u00aa\7\34"+
		"\2\2\u00aa\u00ac\5\26\f\2\u00ab\u00ad\5*\26\2\u00ac\u00ab\3\2\2\2\u00ac"+
		"\u00ad\3\2\2\2\u00ad\u00ae\3\2\2\2\u00ae\u00af\5,\27\2\u00af%\3\2\2\2"+
		"\u00b0\u00b5\7\65\2\2\u00b1\u00b2\7#\2\2\u00b2\u00b3\5\"\22\2\u00b3\u00b4"+
		"\7$\2\2\u00b4\u00b6\3\2\2\2\u00b5\u00b1\3\2\2\2\u00b5\u00b6\3\2\2\2\u00b6"+
		"\'\3\2\2\2\u00b7\u00bc\5\26\f\2\u00b8\u00b9\7/\2\2\u00b9\u00bb\5\26\f"+
		"\2\u00ba\u00b8\3\2\2\2\u00bb\u00be\3\2\2\2\u00bc\u00ba\3\2\2\2\u00bc\u00bd"+
		"\3\2\2\2\u00bd)\3\2\2\2\u00be\u00bc\3\2\2\2\u00bf\u00c0\7(\2\2\u00c0\u00c1"+
		"\7\37\2\2\u00c1\u00c6\5\66\34\2\u00c2\u00c3\7\'\2\2\u00c3\u00c5\5\66\34"+
		"\2\u00c4\u00c2\3\2\2\2\u00c5\u00c8\3\2\2\2\u00c6\u00c4\3\2\2\2\u00c6\u00c7"+
		"\3\2\2\2\u00c7\u00c9\3\2\2\2\u00c8\u00c6\3\2\2\2\u00c9\u00ca\7 \2\2\u00ca"+
		"+\3\2\2\2\u00cb\u00cc\7\33\2\2\u00cc\u00cd\7)\2\2\u00cd\u00dc\7\60\2\2"+
		"\u00ce\u00cf\7\33\2\2\u00cf\u00d0\7*\2\2\u00d0\u00dc\7\60\2\2\u00d1\u00d7"+
		"\7\37\2\2\u00d2\u00d3\5.\30\2\u00d3\u00d4\7\60\2\2\u00d4\u00d6\3\2\2\2"+
		"\u00d5\u00d2\3\2\2\2\u00d6\u00d9\3\2\2\2\u00d7\u00d5\3\2\2\2\u00d7\u00d8"+
		"\3\2\2\2\u00d8\u00da\3\2\2\2\u00d9\u00d7\3\2\2\2\u00da\u00dc\7 \2\2\u00db"+
		"\u00cb\3\2\2\2\u00db\u00ce\3\2\2\2\u00db\u00d1\3\2\2\2\u00dc-\3\2\2\2"+
		"\u00dd\u00e2\5\60\31\2\u00de\u00e2\5\62\32\2\u00df\u00e2\5\64\33\2\u00e0"+
		"\u00e2\5\66\34\2\u00e1\u00dd\3\2\2\2\u00e1\u00de\3\2\2\2\u00e1\u00df\3"+
		"\2\2\2\u00e1\u00e0\3\2\2\2\u00e2/\3\2\2\2\u00e3\u00e4\5\26\f\2\u00e4\u00e5"+
		"\7\33\2\2\u00e5\u00e6\5\66\34\2\u00e6\61\3\2\2\2\u00e7\u00e8\7\65\2\2"+
		"\u00e8\u00e9\7\33\2\2\u00e9\u00ea\5\66\34\2\u00ea\63\3\2\2\2\u00eb\u00ec"+
		"\7\5\2\2\u00ec\u00ed\5\66\34\2\u00ed\u00ee\5,\27\2\u00ee\u00ef\7\6\2\2"+
		"\u00ef\u00f0\5,\27\2\u00f0\65\3\2\2\2\u00f1\u00f2\b\34\1\2\u00f2\u00f3"+
		"\7!\2\2\u00f3\u00f4\5\66\34\2\u00f4\u00f5\7\"\2\2\u00f5\u010d\3\2\2\2"+
		"\u00f6\u00f7\t\3\2\2\u00f7\u010d\5\66\34\21\u00f8\u00f9\7+\2\2\u00f9\u00fa"+
		"\5\26\f\2\u00fa\u00fb\7\34\2\2\u00fb\u00fc\5\66\34\t\u00fc\u010d\3\2\2"+
		"\2\u00fd\u00fe\7\65\2\2\u00fe\u00ff\7-\2\2\u00ff\u010d\7\65\2\2\u0100"+
		"\u0102\7\7\2\2\u0101\u0103\5\26\f\2\u0102\u0101\3\2\2\2\u0102\u0103\3"+
		"\2\2\2\u0103\u0104\3\2\2\2\u0104\u010d\7\7\2\2\u0105\u010d\7\65\2\2\u0106"+
		"\u010d\t\4\2\2\u0107\u0108\t\5\2\2\u0108\u0109\7!\2\2\u0109\u010a\5\66"+
		"\34\2\u010a\u010b\7\"\2\2\u010b\u010d\3\2\2\2\u010c\u00f1\3\2\2\2\u010c"+
		"\u00f6\3\2\2\2\u010c\u00f8\3\2\2\2\u010c\u00fd\3\2\2\2\u010c\u0100\3\2"+
		"\2\2\u010c\u0105\3\2\2\2\u010c\u0106\3\2\2\2\u010c\u0107\3\2\2\2\u010d"+
		"\u0137\3\2\2\2\u010e\u010f\f\22\2\2\u010f\u0110\7\20\2\2\u0110\u0136\5"+
		"\66\34\23\u0111\u0112\f\20\2\2\u0112\u0113\t\6\2\2\u0113\u0136\5\66\34"+
		"\21\u0114\u0115\f\17\2\2\u0115\u0116\t\7\2\2\u0116\u0136\5\66\34\20\u0117"+
		"\u0118\f\16\2\2\u0118\u0119\t\b\2\2\u0119\u0136\5\66\34\17\u011a\u011b"+
		"\f\r\2\2\u011b\u011c\t\t\2\2\u011c\u0136\5\66\34\16\u011d\u011e\f\f\2"+
		"\2\u011e\u011f\7\21\2\2\u011f\u0136\5\66\34\r\u0120\u0121\f\13\2\2\u0121"+
		"\u0122\7\22\2\2\u0122\u0136\5\66\34\f\u0123\u0124\f\n\2\2\u0124\u0125"+
		"\7\36\2\2\u0125\u0136\5\66\34\13\u0126\u0127\f\b\2\2\u0127\u0128\7\7\2"+
		"\2\u0128\u0129\5\66\34\2\u0129\u012a\7.\2\2\u012a\u012b\5\66\34\t\u012b"+
		"\u0136\3\2\2\2\u012c\u012e\f\23\2\2\u012d\u012f\58\35\2\u012e\u012d\3"+
		"\2\2\2\u012e\u012f\3\2\2\2\u012f\u0130\3\2\2\2\u0130\u0132\7!\2\2\u0131"+
		"\u0133\5:\36\2\u0132\u0131\3\2\2\2\u0132\u0133\3\2\2\2\u0133\u0134\3\2"+
		"\2\2\u0134\u0136\7\"\2\2\u0135\u010e\3\2\2\2\u0135\u0111\3\2\2\2\u0135"+
		"\u0114\3\2\2\2\u0135\u0117\3\2\2\2\u0135\u011a\3\2\2\2\u0135\u011d\3\2"+
		"\2\2\u0135\u0120\3\2\2\2\u0135\u0123\3\2\2\2\u0135\u0126\3\2\2\2\u0135"+
		"\u012c\3\2\2\2\u0136\u0139\3\2\2\2\u0137\u0135\3\2\2\2\u0137\u0138\3\2"+
		"\2\2\u0138\67\3\2\2\2\u0139\u0137\3\2\2\2\u013a\u013b\7#\2\2\u013b\u013c"+
		"\5\"\22\2\u013c\u013d\7$\2\2\u013d9\3\2\2\2\u013e\u0143\5\66\34\2\u013f"+
		"\u0140\7/\2\2\u0140\u0142\5\66\34\2\u0141\u013f\3\2\2\2\u0142\u0145\3"+
		"\2\2\2\u0143\u0141\3\2\2\2\u0143\u0144\3\2\2\2\u0144;\3\2\2\2\u0145\u0143"+
		"\3\2\2\2\32BDK[hy\u0080\u0094\u00a0\u00a6\u00ac\u00b5\u00bc\u00c6\u00d7"+
		"\u00db\u00e1\u0102\u010c\u012e\u0132\u0135\u0137\u0143";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}