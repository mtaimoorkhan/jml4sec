// $ANTLR 3.3 Nov 30, 2010 12:50:56 JML.g 2021-08-10 19:52:14

package greenwich.ensuresec.jmlgrammar;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class JMLLexer extends Lexer {
    public static final int EOF=-1;
    public static final int JMLSTART=4;
    public static final int JMLEND=5;
    public static final int PUBLIC_NORMAL_BEHAVIOR=6;
    public static final int COMPROMISED_BEHAVIOR=7;
    public static final int ACTION_BEHAVIOR=8;
    public static final int AT=9;
    public static final int REQUIRES=10;
    public static final int ENSURES=11;
    public static final int ALARMS=12;
    public static final int NOEXCEPTION=13;
    public static final int GHOSTSEQUENCE=14;
    public static final int NAME=15;
    public static final int SEQUENCE=16;
    public static final int ALSO=17;
    public static final int LOG=18;
    public static final int MESSAGE=19;
    public static final int INVALIDATE=20;
    public static final int LOGOUT=21;
    public static final int REDIRECT=22;
    public static final int NOTIFY=23;
    public static final int EMAIL=24;
    public static final int ACTION=25;
    public static final int SEMICOLON=26;
    public static final int IMPLICATION=27;
    public static final int DOT=28;
    public static final int OPERATOR=29;
    public static final int ID=30;
    public static final int AND=31;
    public static final int LINEFEED=32;
    public static final int WS=33;
    public static final int LEFT=34;
    public static final int RIGHT=35;
    public static final int EQUAL=36;
    public static final int COMMA=37;

    // delegates
    // delegators

    public JMLLexer() {;} 
    public JMLLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public JMLLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "JML.g"; }

    // $ANTLR start "JMLSTART"
    public final void mJMLSTART() throws RecognitionException {
        try {
            int _type = JMLSTART;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:14:9: ( '/*@' )
            // JML.g:14:20: '/*@'
            {
            match("/*@"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "JMLSTART"

    // $ANTLR start "JMLEND"
    public final void mJMLEND() throws RecognitionException {
        try {
            int _type = JMLEND;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:15:7: ( '@*/' )
            // JML.g:15:20: '@*/'
            {
            match("@*/"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "JMLEND"

    // $ANTLR start "PUBLIC_NORMAL_BEHAVIOR"
    public final void mPUBLIC_NORMAL_BEHAVIOR() throws RecognitionException {
        try {
            int _type = PUBLIC_NORMAL_BEHAVIOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:16:23: ( 'public normal_behavior' )
            // JML.g:16:25: 'public normal_behavior'
            {
            match("public normal_behavior"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "PUBLIC_NORMAL_BEHAVIOR"

    // $ANTLR start "COMPROMISED_BEHAVIOR"
    public final void mCOMPROMISED_BEHAVIOR() throws RecognitionException {
        try {
            int _type = COMPROMISED_BEHAVIOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:18:21: ( 'compromised_behavior' )
            // JML.g:18:23: 'compromised_behavior'
            {
            match("compromised_behavior"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "COMPROMISED_BEHAVIOR"

    // $ANTLR start "ACTION_BEHAVIOR"
    public final void mACTION_BEHAVIOR() throws RecognitionException {
        try {
            int _type = ACTION_BEHAVIOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:19:16: ( 'action_behavior' )
            // JML.g:19:22: 'action_behavior'
            {
            match("action_behavior"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ACTION_BEHAVIOR"

    // $ANTLR start "AT"
    public final void mAT() throws RecognitionException {
        try {
            int _type = AT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:21:3: ( '@' )
            // JML.g:21:5: '@'
            {
            match('@'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AT"

    // $ANTLR start "REQUIRES"
    public final void mREQUIRES() throws RecognitionException {
        try {
            int _type = REQUIRES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:22:9: ( 'requires' )
            // JML.g:22:18: 'requires'
            {
            match("requires"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "REQUIRES"

    // $ANTLR start "ENSURES"
    public final void mENSURES() throws RecognitionException {
        try {
            int _type = ENSURES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:23:8: ( 'ensures' )
            // JML.g:23:18: 'ensures'
            {
            match("ensures"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ENSURES"

    // $ANTLR start "ALARMS"
    public final void mALARMS() throws RecognitionException {
        try {
            int _type = ALARMS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:24:7: ( 'alarms' )
            // JML.g:24:13: 'alarms'
            {
            match("alarms"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ALARMS"

    // $ANTLR start "NOEXCEPTION"
    public final void mNOEXCEPTION() throws RecognitionException {
        try {
            int _type = NOEXCEPTION;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:25:12: ( 'noException' )
            // JML.g:25:19: 'noException'
            {
            match("noException"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NOEXCEPTION"

    // $ANTLR start "GHOSTSEQUENCE"
    public final void mGHOSTSEQUENCE() throws RecognitionException {
        try {
            int _type = GHOSTSEQUENCE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:26:14: ( '@ghost_seq' )
            // JML.g:26:19: '@ghost_seq'
            {
            match("@ghost_seq"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "GHOSTSEQUENCE"

    // $ANTLR start "NAME"
    public final void mNAME() throws RecognitionException {
        try {
            int _type = NAME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:27:6: ( 'name' )
            // JML.g:27:12: 'name'
            {
            match("name"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NAME"

    // $ANTLR start "SEQUENCE"
    public final void mSEQUENCE() throws RecognitionException {
        try {
            int _type = SEQUENCE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:28:9: ( 'before' | 'after' )
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0=='b') ) {
                alt1=1;
            }
            else if ( (LA1_0=='a') ) {
                alt1=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }
            switch (alt1) {
                case 1 :
                    // JML.g:28:19: 'before'
                    {
                    match("before"); 


                    }
                    break;
                case 2 :
                    // JML.g:28:28: 'after'
                    {
                    match("after"); 


                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SEQUENCE"

    // $ANTLR start "ALSO"
    public final void mALSO() throws RecognitionException {
        try {
            int _type = ALSO;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:29:5: ( 'also' )
            // JML.g:29:12: 'also'
            {
            match("also"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ALSO"

    // $ANTLR start "LOG"
    public final void mLOG() throws RecognitionException {
        try {
            int _type = LOG;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:30:4: ( 'log' )
            // JML.g:30:10: 'log'
            {
            match("log"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LOG"

    // $ANTLR start "MESSAGE"
    public final void mMESSAGE() throws RecognitionException {
        try {
            int _type = MESSAGE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:31:8: ( 'message' )
            // JML.g:31:13: 'message'
            {
            match("message"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "MESSAGE"

    // $ANTLR start "INVALIDATE"
    public final void mINVALIDATE() throws RecognitionException {
        try {
            int _type = INVALIDATE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:32:11: ( 'invalidate' )
            // JML.g:32:15: 'invalidate'
            {
            match("invalidate"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "INVALIDATE"

    // $ANTLR start "LOGOUT"
    public final void mLOGOUT() throws RecognitionException {
        try {
            int _type = LOGOUT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:33:7: ( 'logout' )
            // JML.g:33:12: 'logout'
            {
            match("logout"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LOGOUT"

    // $ANTLR start "REDIRECT"
    public final void mREDIRECT() throws RecognitionException {
        try {
            int _type = REDIRECT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:34:9: ( 'redirect' )
            // JML.g:34:12: 'redirect'
            {
            match("redirect"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "REDIRECT"

    // $ANTLR start "NOTIFY"
    public final void mNOTIFY() throws RecognitionException {
        try {
            int _type = NOTIFY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:35:7: ( 'notify' )
            // JML.g:35:11: 'notify'
            {
            match("notify"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NOTIFY"

    // $ANTLR start "EMAIL"
    public final void mEMAIL() throws RecognitionException {
        try {
            int _type = EMAIL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:36:6: ( 'email' )
            // JML.g:36:11: 'email'
            {
            match("email"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EMAIL"

    // $ANTLR start "ACTION"
    public final void mACTION() throws RecognitionException {
        try {
            int _type = ACTION;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:37:7: ( 'action' )
            // JML.g:37:12: 'action'
            {
            match("action"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ACTION"

    // $ANTLR start "SEMICOLON"
    public final void mSEMICOLON() throws RecognitionException {
        try {
            int _type = SEMICOLON;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:40:10: ( ';' )
            // JML.g:40:17: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SEMICOLON"

    // $ANTLR start "IMPLICATION"
    public final void mIMPLICATION() throws RecognitionException {
        try {
            int _type = IMPLICATION;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:41:12: ( '==>' )
            // JML.g:41:15: '==>'
            {
            match("==>"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "IMPLICATION"

    // $ANTLR start "DOT"
    public final void mDOT() throws RecognitionException {
        try {
            int _type = DOT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:42:4: ( '.' )
            // JML.g:42:18: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "DOT"

    // $ANTLR start "OPERATOR"
    public final void mOPERATOR() throws RecognitionException {
        try {
            int _type = OPERATOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:44:9: ( '==' | '!=' | '>=' | '<=' | '>' | '<' )
            int alt2=6;
            switch ( input.LA(1) ) {
            case '=':
                {
                alt2=1;
                }
                break;
            case '!':
                {
                alt2=2;
                }
                break;
            case '>':
                {
                int LA2_3 = input.LA(2);

                if ( (LA2_3=='=') ) {
                    alt2=3;
                }
                else {
                    alt2=5;}
                }
                break;
            case '<':
                {
                int LA2_4 = input.LA(2);

                if ( (LA2_4=='=') ) {
                    alt2=4;
                }
                else {
                    alt2=6;}
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // JML.g:44:17: '=='
                    {
                    match("=="); 


                    }
                    break;
                case 2 :
                    // JML.g:44:22: '!='
                    {
                    match("!="); 


                    }
                    break;
                case 3 :
                    // JML.g:44:27: '>='
                    {
                    match(">="); 


                    }
                    break;
                case 4 :
                    // JML.g:44:32: '<='
                    {
                    match("<="); 


                    }
                    break;
                case 5 :
                    // JML.g:44:37: '>'
                    {
                    match('>'); 

                    }
                    break;
                case 6 :
                    // JML.g:44:42: '<'
                    {
                    match('<'); 

                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OPERATOR"

    // $ANTLR start "ID"
    public final void mID() throws RecognitionException {
        try {
            int _type = ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:45:3: ( ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' | '@' | '\"' )* )
            // JML.g:45:17: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' | '@' | '\"' )*
            {
            // JML.g:45:17: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' | '@' | '\"' )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='\"'||(LA3_0>='-' && LA3_0<='.')||(LA3_0>='0' && LA3_0<='9')||(LA3_0>='@' && LA3_0<='Z')||LA3_0=='_'||(LA3_0>='a' && LA3_0<='z')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // JML.g:
            	    {
            	    if ( input.LA(1)=='\"'||(input.LA(1)>='-' && input.LA(1)<='.')||(input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='@' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ID"

    // $ANTLR start "AND"
    public final void mAND() throws RecognitionException {
        try {
            int _type = AND;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:47:4: ( '&&' )
            // JML.g:47:9: '&&'
            {
            match("&&"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AND"

    // $ANTLR start "LINEFEED"
    public final void mLINEFEED() throws RecognitionException {
        try {
            int _type = LINEFEED;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:48:9: ( '\\r\\n' )
            // JML.g:48:13: '\\r\\n'
            {
            match("\r\n"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LINEFEED"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:50:3: ( ( ' ' | '\\t' | '\\n' | '\\r' | '\\f' )+ )
            // JML.g:50:18: ( ' ' | '\\t' | '\\n' | '\\r' | '\\f' )+
            {
            // JML.g:50:18: ( ' ' | '\\t' | '\\n' | '\\r' | '\\f' )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='\t' && LA4_0<='\n')||(LA4_0>='\f' && LA4_0<='\r')||LA4_0==' ') ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // JML.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||(input.LA(1)>='\f' && input.LA(1)<='\r')||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WS"

    // $ANTLR start "LEFT"
    public final void mLEFT() throws RecognitionException {
        try {
            int _type = LEFT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:53:5: ( '(' )
            // JML.g:53:10: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LEFT"

    // $ANTLR start "RIGHT"
    public final void mRIGHT() throws RecognitionException {
        try {
            int _type = RIGHT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:54:6: ( ')' )
            // JML.g:54:11: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RIGHT"

    // $ANTLR start "EQUAL"
    public final void mEQUAL() throws RecognitionException {
        try {
            int _type = EQUAL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:55:6: ( '=' )
            // JML.g:55:11: '='
            {
            match('='); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EQUAL"

    // $ANTLR start "COMMA"
    public final void mCOMMA() throws RecognitionException {
        try {
            int _type = COMMA;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // JML.g:56:6: ( ',' )
            // JML.g:56:11: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "COMMA"

    public void mTokens() throws RecognitionException {
        // JML.g:1:8: ( JMLSTART | JMLEND | PUBLIC_NORMAL_BEHAVIOR | COMPROMISED_BEHAVIOR | ACTION_BEHAVIOR | AT | REQUIRES | ENSURES | ALARMS | NOEXCEPTION | GHOSTSEQUENCE | NAME | SEQUENCE | ALSO | LOG | MESSAGE | INVALIDATE | LOGOUT | REDIRECT | NOTIFY | EMAIL | ACTION | SEMICOLON | IMPLICATION | DOT | OPERATOR | ID | AND | LINEFEED | WS | LEFT | RIGHT | EQUAL | COMMA )
        int alt5=34;
        alt5 = dfa5.predict(input);
        switch (alt5) {
            case 1 :
                // JML.g:1:10: JMLSTART
                {
                mJMLSTART(); 

                }
                break;
            case 2 :
                // JML.g:1:19: JMLEND
                {
                mJMLEND(); 

                }
                break;
            case 3 :
                // JML.g:1:26: PUBLIC_NORMAL_BEHAVIOR
                {
                mPUBLIC_NORMAL_BEHAVIOR(); 

                }
                break;
            case 4 :
                // JML.g:1:49: COMPROMISED_BEHAVIOR
                {
                mCOMPROMISED_BEHAVIOR(); 

                }
                break;
            case 5 :
                // JML.g:1:70: ACTION_BEHAVIOR
                {
                mACTION_BEHAVIOR(); 

                }
                break;
            case 6 :
                // JML.g:1:86: AT
                {
                mAT(); 

                }
                break;
            case 7 :
                // JML.g:1:89: REQUIRES
                {
                mREQUIRES(); 

                }
                break;
            case 8 :
                // JML.g:1:98: ENSURES
                {
                mENSURES(); 

                }
                break;
            case 9 :
                // JML.g:1:106: ALARMS
                {
                mALARMS(); 

                }
                break;
            case 10 :
                // JML.g:1:113: NOEXCEPTION
                {
                mNOEXCEPTION(); 

                }
                break;
            case 11 :
                // JML.g:1:125: GHOSTSEQUENCE
                {
                mGHOSTSEQUENCE(); 

                }
                break;
            case 12 :
                // JML.g:1:139: NAME
                {
                mNAME(); 

                }
                break;
            case 13 :
                // JML.g:1:144: SEQUENCE
                {
                mSEQUENCE(); 

                }
                break;
            case 14 :
                // JML.g:1:153: ALSO
                {
                mALSO(); 

                }
                break;
            case 15 :
                // JML.g:1:158: LOG
                {
                mLOG(); 

                }
                break;
            case 16 :
                // JML.g:1:162: MESSAGE
                {
                mMESSAGE(); 

                }
                break;
            case 17 :
                // JML.g:1:170: INVALIDATE
                {
                mINVALIDATE(); 

                }
                break;
            case 18 :
                // JML.g:1:181: LOGOUT
                {
                mLOGOUT(); 

                }
                break;
            case 19 :
                // JML.g:1:188: REDIRECT
                {
                mREDIRECT(); 

                }
                break;
            case 20 :
                // JML.g:1:197: NOTIFY
                {
                mNOTIFY(); 

                }
                break;
            case 21 :
                // JML.g:1:204: EMAIL
                {
                mEMAIL(); 

                }
                break;
            case 22 :
                // JML.g:1:210: ACTION
                {
                mACTION(); 

                }
                break;
            case 23 :
                // JML.g:1:217: SEMICOLON
                {
                mSEMICOLON(); 

                }
                break;
            case 24 :
                // JML.g:1:227: IMPLICATION
                {
                mIMPLICATION(); 

                }
                break;
            case 25 :
                // JML.g:1:239: DOT
                {
                mDOT(); 

                }
                break;
            case 26 :
                // JML.g:1:243: OPERATOR
                {
                mOPERATOR(); 

                }
                break;
            case 27 :
                // JML.g:1:252: ID
                {
                mID(); 

                }
                break;
            case 28 :
                // JML.g:1:255: AND
                {
                mAND(); 

                }
                break;
            case 29 :
                // JML.g:1:259: LINEFEED
                {
                mLINEFEED(); 

                }
                break;
            case 30 :
                // JML.g:1:268: WS
                {
                mWS(); 

                }
                break;
            case 31 :
                // JML.g:1:271: LEFT
                {
                mLEFT(); 

                }
                break;
            case 32 :
                // JML.g:1:276: RIGHT
                {
                mRIGHT(); 

                }
                break;
            case 33 :
                // JML.g:1:282: EQUAL
                {
                mEQUAL(); 

                }
                break;
            case 34 :
                // JML.g:1:288: COMMA
                {
                mCOMMA(); 

                }
                break;

        }

    }


    protected DFA5 dfa5 = new DFA5(this);
    static final String DFA5_eotS =
        "\1\21\1\uffff\1\32\12\21\1\uffff\1\52\1\53\3\uffff\1\24\5\uffff"+
        "\1\21\1\uffff\16\21\1\20\2\uffff\1\100\17\21\1\121\2\21\2\uffff"+
        "\5\21\1\131\7\21\1\141\2\21\1\uffff\7\21\1\uffff\1\153\3\21\1\157"+
        "\2\21\1\uffff\7\21\1\172\1\173\1\uffff\3\21\1\uffff\1\21\1\u0080"+
        "\1\153\1\u0081\3\21\1\uffff\2\21\2\uffff\2\21\1\u0089\1\21\2\uffff"+
        "\1\u008b\4\21\1\u0090\1\u0091\1\uffff\1\21\1\uffff\4\21\2\uffff"+
        "\2\21\1\u0099\3\21\1\u009d\1\uffff\2\21\1\u00a0\1\uffff\2\21\1\uffff"+
        "\5\21\1\u00a8\1\21\1\uffff\3\21\1\u00ad\1\uffff";
    static final String DFA5_eofS =
        "\u00ae\uffff";
    static final String DFA5_minS =
        "\1\11\1\uffff\1\42\1\165\1\157\1\143\1\145\1\155\1\141\1\145\1\157"+
        "\1\145\1\156\1\uffff\1\75\1\42\3\uffff\1\12\5\uffff\1\150\1\uffff"+
        "\1\142\1\155\1\164\1\141\1\164\1\144\1\163\1\141\1\105\1\155\1\146"+
        "\1\147\1\163\1\166\1\76\2\uffff\1\11\1\157\1\154\1\160\1\151\1\162"+
        "\1\157\1\145\1\165\1\151\1\165\1\151\1\170\1\151\1\145\1\157\1\42"+
        "\1\163\1\141\2\uffff\1\163\1\151\1\162\1\157\1\155\1\42\1\162\1"+
        "\151\2\162\1\154\1\143\1\146\1\42\1\162\1\165\1\uffff\1\141\1\154"+
        "\1\164\1\143\1\157\1\156\1\163\1\uffff\1\42\1\162\2\145\1\42\1\145"+
        "\1\171\1\uffff\1\145\1\164\1\147\1\151\1\137\1\40\1\155\2\42\1\uffff"+
        "\1\145\1\143\1\163\1\uffff\1\160\3\42\1\145\1\144\1\163\1\uffff"+
        "\1\151\1\142\2\uffff\1\163\1\164\1\42\1\164\2\uffff\1\42\1\141\1"+
        "\145\1\163\1\145\2\42\1\uffff\1\151\1\uffff\1\164\1\161\1\145\1"+
        "\150\2\uffff\1\157\1\145\1\42\1\144\1\141\1\156\1\42\1\uffff\1\137"+
        "\1\166\1\42\1\uffff\1\142\1\151\1\uffff\1\145\1\157\1\150\1\162"+
        "\1\141\1\42\1\166\1\uffff\1\151\1\157\1\162\1\42\1\uffff";
    static final String DFA5_maxS =
        "\1\162\1\uffff\1\172\1\165\1\157\1\154\1\145\1\156\1\157\1\145\1"+
        "\157\1\145\1\156\1\uffff\1\75\1\172\3\uffff\1\12\5\uffff\1\150\1"+
        "\uffff\1\142\1\155\1\164\1\163\1\164\1\161\1\163\1\141\1\164\1\155"+
        "\1\146\1\147\1\163\1\166\1\76\2\uffff\1\40\1\157\1\154\1\160\1\151"+
        "\1\162\1\157\1\145\1\165\1\151\1\165\1\151\1\170\1\151\1\145\1\157"+
        "\1\172\1\163\1\141\2\uffff\1\163\1\151\1\162\1\157\1\155\1\172\1"+
        "\162\1\151\2\162\1\154\1\143\1\146\1\172\1\162\1\165\1\uffff\1\141"+
        "\1\154\1\164\1\143\1\157\1\156\1\163\1\uffff\1\172\1\162\2\145\1"+
        "\172\1\145\1\171\1\uffff\1\145\1\164\1\147\1\151\1\137\1\40\1\155"+
        "\2\172\1\uffff\1\145\1\143\1\163\1\uffff\1\160\3\172\1\145\1\144"+
        "\1\163\1\uffff\1\151\1\142\2\uffff\1\163\1\164\1\172\1\164\2\uffff"+
        "\1\172\1\141\1\145\1\163\1\145\2\172\1\uffff\1\151\1\uffff\1\164"+
        "\1\161\1\145\1\150\2\uffff\1\157\1\145\1\172\1\144\1\141\1\156\1"+
        "\172\1\uffff\1\137\1\166\1\172\1\uffff\1\142\1\151\1\uffff\1\145"+
        "\1\157\1\150\1\162\1\141\1\172\1\166\1\uffff\1\151\1\157\1\162\1"+
        "\172\1\uffff";
    static final String DFA5_acceptS =
        "\1\uffff\1\1\13\uffff\1\27\2\uffff\1\32\1\33\1\34\1\uffff\1\36\1"+
        "\37\1\40\1\42\1\2\1\uffff\1\6\17\uffff\1\41\1\31\23\uffff\1\30\1"+
        "\35\20\uffff\1\17\7\uffff\1\16\7\uffff\1\14\11\uffff\1\15\3\uffff"+
        "\1\25\7\uffff\1\3\2\uffff\1\26\1\11\4\uffff\1\24\1\22\7\uffff\1"+
        "\10\1\uffff\1\20\4\uffff\1\7\1\23\7\uffff\1\13\3\uffff\1\21\2\uffff"+
        "\1\12\7\uffff\1\5\4\uffff\1\4";
    static final String DFA5_specialS =
        "\u00ae\uffff}>";
    static final String[] DFA5_transitionS = {
            "\2\24\1\uffff\1\24\1\23\22\uffff\1\24\1\20\4\uffff\1\22\1\uffff"+
            "\1\25\1\26\2\uffff\1\27\1\uffff\1\17\1\1\13\uffff\1\15\1\20"+
            "\1\16\1\20\1\uffff\1\2\40\uffff\1\5\1\11\1\4\1\uffff\1\7\3\uffff"+
            "\1\14\2\uffff\1\12\1\13\1\10\1\uffff\1\3\1\uffff\1\6",
            "",
            "\1\21\7\uffff\1\30\2\uffff\2\21\1\uffff\12\21\6\uffff\33\21"+
            "\4\uffff\1\21\1\uffff\6\21\1\31\23\21",
            "\1\33",
            "\1\34",
            "\1\35\2\uffff\1\37\5\uffff\1\36",
            "\1\40",
            "\1\42\1\41",
            "\1\44\15\uffff\1\43",
            "\1\45",
            "\1\46",
            "\1\47",
            "\1\50",
            "",
            "\1\51",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "",
            "",
            "",
            "\1\54",
            "",
            "",
            "",
            "",
            "",
            "\1\55",
            "",
            "\1\56",
            "\1\57",
            "\1\60",
            "\1\61\21\uffff\1\62",
            "\1\63",
            "\1\65\14\uffff\1\64",
            "\1\66",
            "\1\67",
            "\1\70\56\uffff\1\71",
            "\1\72",
            "\1\73",
            "\1\74",
            "\1\75",
            "\1\76",
            "\1\77",
            "",
            "",
            "\2\24\1\uffff\2\24\22\uffff\1\24",
            "\1\101",
            "\1\102",
            "\1\103",
            "\1\104",
            "\1\105",
            "\1\106",
            "\1\107",
            "\1\110",
            "\1\111",
            "\1\112",
            "\1\113",
            "\1\114",
            "\1\115",
            "\1\116",
            "\1\117",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\16\21\1\120\13\21",
            "\1\122",
            "\1\123",
            "",
            "",
            "\1\124",
            "\1\125",
            "\1\126",
            "\1\127",
            "\1\130",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\132",
            "\1\133",
            "\1\134",
            "\1\135",
            "\1\136",
            "\1\137",
            "\1\140",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\142",
            "\1\143",
            "",
            "\1\144",
            "\1\145",
            "\1\146",
            "\1\147",
            "\1\150",
            "\1\151",
            "\1\152",
            "",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\154",
            "\1\155",
            "\1\156",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\160",
            "\1\161",
            "",
            "\1\162",
            "\1\163",
            "\1\164",
            "\1\165",
            "\1\166",
            "\1\167",
            "\1\170",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\171"+
            "\1\uffff\32\21",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "",
            "\1\174",
            "\1\175",
            "\1\176",
            "",
            "\1\177",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\u0082",
            "\1\u0083",
            "\1\u0084",
            "",
            "\1\u0085",
            "\1\u0086",
            "",
            "",
            "\1\u0087",
            "\1\u0088",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\u008a",
            "",
            "",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\u008c",
            "\1\u008d",
            "\1\u008e",
            "\1\u008f",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "",
            "\1\u0092",
            "",
            "\1\u0093",
            "\1\u0094",
            "\1\u0095",
            "\1\u0096",
            "",
            "",
            "\1\u0097",
            "\1\u0098",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\u009a",
            "\1\u009b",
            "\1\u009c",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "",
            "\1\u009e",
            "\1\u009f",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "",
            "\1\u00a1",
            "\1\u00a2",
            "",
            "\1\u00a3",
            "\1\u00a4",
            "\1\u00a5",
            "\1\u00a6",
            "\1\u00a7",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            "\1\u00a9",
            "",
            "\1\u00aa",
            "\1\u00ab",
            "\1\u00ac",
            "\1\21\12\uffff\2\21\1\uffff\12\21\6\uffff\33\21\4\uffff\1\21"+
            "\1\uffff\32\21",
            ""
    };

    static final short[] DFA5_eot = DFA.unpackEncodedString(DFA5_eotS);
    static final short[] DFA5_eof = DFA.unpackEncodedString(DFA5_eofS);
    static final char[] DFA5_min = DFA.unpackEncodedStringToUnsignedChars(DFA5_minS);
    static final char[] DFA5_max = DFA.unpackEncodedStringToUnsignedChars(DFA5_maxS);
    static final short[] DFA5_accept = DFA.unpackEncodedString(DFA5_acceptS);
    static final short[] DFA5_special = DFA.unpackEncodedString(DFA5_specialS);
    static final short[][] DFA5_transition;

    static {
        int numStates = DFA5_transitionS.length;
        DFA5_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA5_transition[i] = DFA.unpackEncodedString(DFA5_transitionS[i]);
        }
    }

    class DFA5 extends DFA {

        public DFA5(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 5;
            this.eot = DFA5_eot;
            this.eof = DFA5_eof;
            this.min = DFA5_min;
            this.max = DFA5_max;
            this.accept = DFA5_accept;
            this.special = DFA5_special;
            this.transition = DFA5_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( JMLSTART | JMLEND | PUBLIC_NORMAL_BEHAVIOR | COMPROMISED_BEHAVIOR | ACTION_BEHAVIOR | AT | REQUIRES | ENSURES | ALARMS | NOEXCEPTION | GHOSTSEQUENCE | NAME | SEQUENCE | ALSO | LOG | MESSAGE | INVALIDATE | LOGOUT | REDIRECT | NOTIFY | EMAIL | ACTION | SEMICOLON | IMPLICATION | DOT | OPERATOR | ID | AND | LINEFEED | WS | LEFT | RIGHT | EQUAL | COMMA );";
        }
    }
 

}