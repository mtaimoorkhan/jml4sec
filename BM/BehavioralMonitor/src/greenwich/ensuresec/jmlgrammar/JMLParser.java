// $ANTLR 3.3 Nov 30, 2010 12:50:56 JML.g 2021-08-10 19:52:14

package greenwich.ensuresec.jmlgrammar;
import greenwich.ensuresec.structure.JMLStore;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class JMLParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "JMLSTART", "JMLEND", "PUBLIC_NORMAL_BEHAVIOR", "COMPROMISED_BEHAVIOR", "ACTION_BEHAVIOR", "AT", "REQUIRES", "ENSURES", "ALARMS", "NOEXCEPTION", "GHOSTSEQUENCE", "NAME", "SEQUENCE", "ALSO", "LOG", "MESSAGE", "INVALIDATE", "LOGOUT", "REDIRECT", "NOTIFY", "EMAIL", "ACTION", "SEMICOLON", "IMPLICATION", "DOT", "OPERATOR", "ID", "AND", "LINEFEED", "WS", "LEFT", "RIGHT", "EQUAL", "COMMA"
    };
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


        public JMLParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public JMLParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return JMLParser.tokenNames; }
    public String getGrammarFileName() { return "JML.g"; }



    // $ANTLR start "jmlSpecifications"
    // JML.g:73:1: jmlSpecifications : ( jmlCompromisedSpecs | jmlGhostSpecs | jmlActionSpecs )* ;
    public final void jmlSpecifications() throws RecognitionException {
        try {
            // JML.g:73:18: ( ( jmlCompromisedSpecs | jmlGhostSpecs | jmlActionSpecs )* )
            // JML.g:73:20: ( jmlCompromisedSpecs | jmlGhostSpecs | jmlActionSpecs )*
            {
            // JML.g:73:20: ( jmlCompromisedSpecs | jmlGhostSpecs | jmlActionSpecs )*
            loop1:
            do {
                int alt1=4;
                switch ( input.LA(1) ) {
                case COMPROMISED_BEHAVIOR:
                    {
                    alt1=1;
                    }
                    break;
                case GHOSTSEQUENCE:
                    {
                    alt1=2;
                    }
                    break;
                case ALSO:
                    {
                    alt1=3;
                    }
                    break;

                }

                switch (alt1) {
            	case 1 :
            	    // JML.g:73:21: jmlCompromisedSpecs
            	    {
            	    pushFollow(FOLLOW_jmlCompromisedSpecs_in_jmlSpecifications480);
            	    jmlCompromisedSpecs();

            	    state._fsp--;


            	    }
            	    break;
            	case 2 :
            	    // JML.g:73:41: jmlGhostSpecs
            	    {
            	    pushFollow(FOLLOW_jmlGhostSpecs_in_jmlSpecifications482);
            	    jmlGhostSpecs();

            	    state._fsp--;


            	    }
            	    break;
            	case 3 :
            	    // JML.g:73:57: jmlActionSpecs
            	    {
            	    pushFollow(FOLLOW_jmlActionSpecs_in_jmlSpecifications486);
            	    jmlActionSpecs();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlSpecifications"


    // $ANTLR start "jmlActionSpecs"
    // JML.g:77:1: jmlActionSpecs : ALSO ACTION_BEHAVIOR ( actClause )* ;
    public final void jmlActionSpecs() throws RecognitionException {
        try {
            // JML.g:77:15: ( ALSO ACTION_BEHAVIOR ( actClause )* )
            // JML.g:77:17: ALSO ACTION_BEHAVIOR ( actClause )*
            {
            match(input,ALSO,FOLLOW_ALSO_in_jmlActionSpecs497); 
            match(input,ACTION_BEHAVIOR,FOLLOW_ACTION_BEHAVIOR_in_jmlActionSpecs499); 
            // JML.g:77:38: ( actClause )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==ACTION) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // JML.g:77:39: actClause
            	    {
            	    pushFollow(FOLLOW_actClause_in_jmlActionSpecs502);
            	    actClause();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlActionSpecs"


    // $ANTLR start "actClause"
    // JML.g:80:1: actClause : (clause= ACTION ) actionClause SEMICOLON ;
    public final void actClause() throws RecognitionException {
        Token clause=null;

        try {
            // JML.g:80:10: ( (clause= ACTION ) actionClause SEMICOLON )
            // JML.g:80:12: (clause= ACTION ) actionClause SEMICOLON
            {
            // JML.g:80:12: (clause= ACTION )
            // JML.g:80:13: clause= ACTION
            {
            clause=(Token)match(input,ACTION,FOLLOW_ACTION_in_actClause518); 

            }


            	JMLStore.setClauseType((clause!=null?clause.getText():null));
            	System.out.println("Parsed Clause: "+(clause!=null?clause.getText():null));

            pushFollow(FOLLOW_actionClause_in_actClause523);
            actionClause();

            state._fsp--;

            match(input,SEMICOLON,FOLLOW_SEMICOLON_in_actClause526); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "actClause"


    // $ANTLR start "actionClause"
    // JML.g:86:1: actionClause : jmlMethodCall IMPLICATION ( rightSideClause ) ;
    public final void actionClause() throws RecognitionException {
        try {
            // JML.g:86:13: ( jmlMethodCall IMPLICATION ( rightSideClause ) )
            // JML.g:86:15: jmlMethodCall IMPLICATION ( rightSideClause )
            {
            pushFollow(FOLLOW_jmlMethodCall_in_actionClause534);
            jmlMethodCall();

            state._fsp--;

            match(input,IMPLICATION,FOLLOW_IMPLICATION_in_actionClause536); 
            // JML.g:86:41: ( rightSideClause )
            // JML.g:86:42: rightSideClause
            {
            pushFollow(FOLLOW_rightSideClause_in_actionClause539);
            rightSideClause();

            state._fsp--;


            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "actionClause"


    // $ANTLR start "rightSideClause"
    // JML.g:89:1: rightSideClause : mName= ID LEFT ( rightSideMethodParam )* RIGHT ;
    public final void rightSideClause() throws RecognitionException {
        Token mName=null;

        try {
            // JML.g:89:16: (mName= ID LEFT ( rightSideMethodParam )* RIGHT )
            // JML.g:89:18: mName= ID LEFT ( rightSideMethodParam )* RIGHT
            {
            mName=(Token)match(input,ID,FOLLOW_ID_in_rightSideClause551); 
            JMLStore.addRightSideMethCall((mName!=null?mName.getText():null));
            match(input,LEFT,FOLLOW_LEFT_in_rightSideClause555); 
            // JML.g:89:78: ( rightSideMethodParam )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0==ID||LA3_0==COMMA) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // JML.g:89:79: rightSideMethodParam
            	    {
            	    pushFollow(FOLLOW_rightSideMethodParam_in_rightSideClause558);
            	    rightSideMethodParam();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);

            match(input,RIGHT,FOLLOW_RIGHT_in_rightSideClause562); 



            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "rightSideClause"


    // $ANTLR start "rightSideMethodParam"
    // JML.g:93:1: rightSideMethodParam : (pName= ID | COMMA pName= ID ) ;
    public final void rightSideMethodParam() throws RecognitionException {
        Token pName=null;

        try {
            // JML.g:93:21: ( (pName= ID | COMMA pName= ID ) )
            // JML.g:93:23: (pName= ID | COMMA pName= ID )
            {
            // JML.g:93:23: (pName= ID | COMMA pName= ID )
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==ID) ) {
                alt4=1;
            }
            else if ( (LA4_0==COMMA) ) {
                alt4=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 4, 0, input);

                throw nvae;
            }
            switch (alt4) {
                case 1 :
                    // JML.g:93:24: pName= ID
                    {
                    pName=(Token)match(input,ID,FOLLOW_ID_in_rightSideMethodParam574); 

                    }
                    break;
                case 2 :
                    // JML.g:93:34: COMMA pName= ID
                    {
                    match(input,COMMA,FOLLOW_COMMA_in_rightSideMethodParam577); 
                    pName=(Token)match(input,ID,FOLLOW_ID_in_rightSideMethodParam581); 

                    }
                    break;

            }


            	JMLStore.addRightSideMethCallParameter((pName!=null?pName.getText():null));
            	System.out.println("param: "+(pName!=null?pName.getText():null));


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "rightSideMethodParam"


    // $ANTLR start "jmlGhostSpecs"
    // JML.g:101:1: jmlGhostSpecs : GHOSTSEQUENCE LEFT NAME EQUAL var= ID RIGHT ;
    public final void jmlGhostSpecs() throws RecognitionException {
        Token var=null;

        try {
            // JML.g:101:14: ( GHOSTSEQUENCE LEFT NAME EQUAL var= ID RIGHT )
            // JML.g:101:16: GHOSTSEQUENCE LEFT NAME EQUAL var= ID RIGHT
            {
            match(input,GHOSTSEQUENCE,FOLLOW_GHOSTSEQUENCE_in_jmlGhostSpecs594); 
            match(input,LEFT,FOLLOW_LEFT_in_jmlGhostSpecs596); 
            match(input,NAME,FOLLOW_NAME_in_jmlGhostSpecs598); 
            match(input,EQUAL,FOLLOW_EQUAL_in_jmlGhostSpecs600); 
            var=(Token)match(input,ID,FOLLOW_ID_in_jmlGhostSpecs606); 
            match(input,RIGHT,FOLLOW_RIGHT_in_jmlGhostSpecs609); 

            	System.out.println("The variable name is " + (var!=null?var.getText():null) );
            	JMLStore.setGhostName((var!=null?var.getText():null));


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlGhostSpecs"


    // $ANTLR start "jmlCompromisedSpecs"
    // JML.g:106:1: jmlCompromisedSpecs : COMPROMISED_BEHAVIOR ( COMMA | jmlClause )* ;
    public final void jmlCompromisedSpecs() throws RecognitionException {
        try {
            // JML.g:106:20: ( COMPROMISED_BEHAVIOR ( COMMA | jmlClause )* )
            // JML.g:106:22: COMPROMISED_BEHAVIOR ( COMMA | jmlClause )*
            {
            match(input,COMPROMISED_BEHAVIOR,FOLLOW_COMPROMISED_BEHAVIOR_in_jmlCompromisedSpecs618); 
            // JML.g:106:45: ( COMMA | jmlClause )*
            loop5:
            do {
                int alt5=3;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==COMMA) ) {
                    alt5=1;
                }
                else if ( ((LA5_0>=REQUIRES && LA5_0<=NOEXCEPTION)||LA5_0==SEQUENCE) ) {
                    alt5=2;
                }


                switch (alt5) {
            	case 1 :
            	    // JML.g:106:46: COMMA
            	    {
            	    match(input,COMMA,FOLLOW_COMMA_in_jmlCompromisedSpecs623); 

            	    }
            	    break;
            	case 2 :
            	    // JML.g:106:54: jmlClause
            	    {
            	    pushFollow(FOLLOW_jmlClause_in_jmlCompromisedSpecs627);
            	    jmlClause();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop5;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlCompromisedSpecs"


    // $ANTLR start "jmlClause"
    // JML.g:109:1: jmlClause : (clause= REQUIRES | clause= ENSURES | clause= ALARMS | clause= SEQUENCE | clause= NOEXCEPTION ) jmlCond SEMICOLON ;
    public final void jmlClause() throws RecognitionException {
        Token clause=null;

        try {
            // JML.g:109:10: ( (clause= REQUIRES | clause= ENSURES | clause= ALARMS | clause= SEQUENCE | clause= NOEXCEPTION ) jmlCond SEMICOLON )
            // JML.g:109:12: (clause= REQUIRES | clause= ENSURES | clause= ALARMS | clause= SEQUENCE | clause= NOEXCEPTION ) jmlCond SEMICOLON
            {
            // JML.g:109:12: (clause= REQUIRES | clause= ENSURES | clause= ALARMS | clause= SEQUENCE | clause= NOEXCEPTION )
            int alt6=5;
            switch ( input.LA(1) ) {
            case REQUIRES:
                {
                alt6=1;
                }
                break;
            case ENSURES:
                {
                alt6=2;
                }
                break;
            case ALARMS:
                {
                alt6=3;
                }
                break;
            case SEQUENCE:
                {
                alt6=4;
                }
                break;
            case NOEXCEPTION:
                {
                alt6=5;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }

            switch (alt6) {
                case 1 :
                    // JML.g:109:13: clause= REQUIRES
                    {
                    clause=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_jmlClause641); 

                    }
                    break;
                case 2 :
                    // JML.g:109:30: clause= ENSURES
                    {
                    clause=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_jmlClause646); 

                    }
                    break;
                case 3 :
                    // JML.g:109:47: clause= ALARMS
                    {
                    clause=(Token)match(input,ALARMS,FOLLOW_ALARMS_in_jmlClause652); 

                    }
                    break;
                case 4 :
                    // JML.g:109:63: clause= SEQUENCE
                    {
                    clause=(Token)match(input,SEQUENCE,FOLLOW_SEQUENCE_in_jmlClause658); 

                    }
                    break;
                case 5 :
                    // JML.g:109:81: clause= NOEXCEPTION
                    {
                    clause=(Token)match(input,NOEXCEPTION,FOLLOW_NOEXCEPTION_in_jmlClause666); 

                    }
                    break;

            }

             
            	JMLStore.setClauseType((clause!=null?clause.getText():null));System.out.println("Parsed Clause: "+(clause!=null?clause.getText():null));
            	
            pushFollow(FOLLOW_jmlCond_in_jmlClause671);
            jmlCond();

            state._fsp--;

            match(input,SEMICOLON,FOLLOW_SEMICOLON_in_jmlClause674); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlClause"


    // $ANTLR start "jmlCond"
    // JML.g:114:1: jmlCond : ( AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException )* ;
    public final void jmlCond() throws RecognitionException {
        try {
            // JML.g:114:8: ( ( AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException )* )
            // JML.g:114:12: ( AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException )*
            {
            // JML.g:114:12: ( AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException )*
            loop7:
            do {
                int alt7=6;
                alt7 = dfa7.predict(input);
                switch (alt7) {
            	case 1 :
            	    // JML.g:114:13: AND
            	    {
            	    match(input,AND,FOLLOW_AND_in_jmlCond685); 

            	    }
            	    break;
            	case 2 :
            	    // JML.g:114:19: jmlBinCon
            	    {
            	    pushFollow(FOLLOW_jmlBinCon_in_jmlCond689);
            	    jmlBinCon();

            	    state._fsp--;


            	    }
            	    break;
            	case 3 :
            	    // JML.g:114:31: jmlMethodCall
            	    {
            	    pushFollow(FOLLOW_jmlMethodCall_in_jmlCond693);
            	    jmlMethodCall();

            	    state._fsp--;


            	    }
            	    break;
            	case 4 :
            	    // JML.g:114:47: jmlAlarm
            	    {
            	    pushFollow(FOLLOW_jmlAlarm_in_jmlCond697);
            	    jmlAlarm();

            	    state._fsp--;


            	    }
            	    break;
            	case 5 :
            	    // JML.g:114:58: jmlException
            	    {
            	    pushFollow(FOLLOW_jmlException_in_jmlCond701);
            	    jmlException();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlCond"


    // $ANTLR start "jmlBinCon"
    // JML.g:117:1: jmlBinCon : leftOp= ID con= OPERATOR rightOp= ID ;
    public final void jmlBinCon() throws RecognitionException {
        Token leftOp=null;
        Token con=null;
        Token rightOp=null;

        try {
            // JML.g:117:10: (leftOp= ID con= OPERATOR rightOp= ID )
            // JML.g:117:12: leftOp= ID con= OPERATOR rightOp= ID
            {
            leftOp=(Token)match(input,ID,FOLLOW_ID_in_jmlBinCon715); 
            con=(Token)match(input,OPERATOR,FOLLOW_OPERATOR_in_jmlBinCon719); 
            rightOp=(Token)match(input,ID,FOLLOW_ID_in_jmlBinCon724); 


            	JMLStore.addBinaryCon((leftOp!=null?leftOp.getText():null),(con!=null?con.getText():null),(rightOp!=null?rightOp.getText():null));	
            	System.out.println("Binary con added: "+ (con!=null?con.getText():null));


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlBinCon"


    // $ANTLR start "jmlAlarm"
    // JML.g:126:1: jmlAlarm : ( jmlMethodCall | jmlBinCon ) IMPLICATION threat= ID ;
    public final void jmlAlarm() throws RecognitionException {
        Token threat=null;

        try {
            // JML.g:126:9: ( ( jmlMethodCall | jmlBinCon ) IMPLICATION threat= ID )
            // JML.g:126:11: ( jmlMethodCall | jmlBinCon ) IMPLICATION threat= ID
            {
            // JML.g:126:11: ( jmlMethodCall | jmlBinCon )
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==ID) ) {
                int LA8_1 = input.LA(2);

                if ( (LA8_1==OPERATOR) ) {
                    alt8=2;
                }
                else if ( (LA8_1==LEFT) ) {
                    alt8=1;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 8, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 8, 0, input);

                throw nvae;
            }
            switch (alt8) {
                case 1 :
                    // JML.g:126:12: jmlMethodCall
                    {
                    pushFollow(FOLLOW_jmlMethodCall_in_jmlAlarm736);
                    jmlMethodCall();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // JML.g:126:28: jmlBinCon
                    {
                    pushFollow(FOLLOW_jmlBinCon_in_jmlAlarm740);
                    jmlBinCon();

                    state._fsp--;


                    }
                    break;

            }

            match(input,IMPLICATION,FOLLOW_IMPLICATION_in_jmlAlarm743); 
            threat=(Token)match(input,ID,FOLLOW_ID_in_jmlAlarm747); 

            	
            	JMLStore.AddAlarms((threat!=null?threat.getText():null));
            	System.out.println("Threat : "+ (threat!=null?threat.getText():null));


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlAlarm"


    // $ANTLR start "jmlMethodCall"
    // JML.g:134:1: jmlMethodCall : methodCall con= OPERATOR rightOp= ID ;
    public final void jmlMethodCall() throws RecognitionException {
        Token con=null;
        Token rightOp=null;

        try {
            // JML.g:134:14: ( methodCall con= OPERATOR rightOp= ID )
            // JML.g:134:16: methodCall con= OPERATOR rightOp= ID
            {
            pushFollow(FOLLOW_methodCall_in_jmlMethodCall758);
            methodCall();

            state._fsp--;

            con=(Token)match(input,OPERATOR,FOLLOW_OPERATOR_in_jmlMethodCall762); 
            rightOp=(Token)match(input,ID,FOLLOW_ID_in_jmlMethodCall767); 

            	
            	JMLStore.addMethCallCond((con!=null?con.getText():null),(rightOp!=null?rightOp.getText():null));
            	


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlMethodCall"


    // $ANTLR start "methodCall"
    // JML.g:141:1: methodCall : mName= ID LEFT ( methodParam )* RIGHT ;
    public final void methodCall() throws RecognitionException {
        Token mName=null;

        try {
            // JML.g:141:11: (mName= ID LEFT ( methodParam )* RIGHT )
            // JML.g:141:13: mName= ID LEFT ( methodParam )* RIGHT
            {
            mName=(Token)match(input,ID,FOLLOW_ID_in_methodCall779); 
            JMLStore.addMethCall((mName!=null?mName.getText():null));
            match(input,LEFT,FOLLOW_LEFT_in_methodCall783); 
            // JML.g:141:64: ( methodParam )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==ID||LA9_0==COMMA) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // JML.g:141:65: methodParam
            	    {
            	    pushFollow(FOLLOW_methodParam_in_methodCall786);
            	    methodParam();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);

            match(input,RIGHT,FOLLOW_RIGHT_in_methodCall790); 



            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "methodCall"


    // $ANTLR start "methodParam"
    // JML.g:145:1: methodParam : (pName= ID | COMMA pName= ID ) ;
    public final void methodParam() throws RecognitionException {
        Token pName=null;

        try {
            // JML.g:145:12: ( (pName= ID | COMMA pName= ID ) )
            // JML.g:145:14: (pName= ID | COMMA pName= ID )
            {
            // JML.g:145:14: (pName= ID | COMMA pName= ID )
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==ID) ) {
                alt10=1;
            }
            else if ( (LA10_0==COMMA) ) {
                alt10=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 10, 0, input);

                throw nvae;
            }
            switch (alt10) {
                case 1 :
                    // JML.g:145:15: pName= ID
                    {
                    pName=(Token)match(input,ID,FOLLOW_ID_in_methodParam802); 

                    }
                    break;
                case 2 :
                    // JML.g:145:25: COMMA pName= ID
                    {
                    match(input,COMMA,FOLLOW_COMMA_in_methodParam805); 
                    pName=(Token)match(input,ID,FOLLOW_ID_in_methodParam809); 

                    }
                    break;

            }


            	JMLStore.addMethCallParameter((pName!=null?pName.getText():null));
            	System.out.println("param: "+(pName!=null?pName.getText():null));


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "methodParam"


    // $ANTLR start "jmlException"
    // JML.g:151:1: jmlException : value= ID ;
    public final void jmlException() throws RecognitionException {
        Token value=null;

        try {
            // JML.g:151:13: (value= ID )
            // JML.g:151:15: value= ID
            {
            value=(Token)match(input,ID,FOLLOW_ID_in_jmlException823); 
             System.out.println("exception-value: "+(value!=null?value.getText():null)); JMLStore.AddException((value!=null?value.getText():null));  

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "jmlException"

    // Delegated rules


    protected DFA7 dfa7 = new DFA7(this);
    static final String DFA7_eotS =
        "\21\uffff";
    static final String DFA7_eofS =
        "\21\uffff";
    static final String DFA7_minS =
        "\1\32\2\uffff\1\32\2\36\1\uffff\1\32\2\36\1\35\2\uffff\2\36\1\32"+
        "\1\uffff";
    static final String DFA7_maxS =
        "\1\37\2\uffff\1\42\1\36\1\45\1\uffff\1\37\1\45\1\36\1\35\2\uffff"+
        "\1\45\1\36\1\37\1\uffff";
    static final String DFA7_acceptS =
        "\1\uffff\1\6\1\1\3\uffff\1\5\4\uffff\1\2\1\4\3\uffff\1\3";
    static final String DFA7_specialS =
        "\21\uffff}>";
    static final String[] DFA7_transitionS = {
            "\1\1\3\uffff\1\3\1\2",
            "",
            "",
            "\1\6\2\uffff\1\4\2\6\2\uffff\1\5",
            "\1\7",
            "\1\10\4\uffff\1\12\1\uffff\1\11",
            "",
            "\1\13\1\14\2\uffff\2\13",
            "\1\10\4\uffff\1\12\1\uffff\1\11",
            "\1\15",
            "\1\16",
            "",
            "",
            "\1\10\4\uffff\1\12\1\uffff\1\11",
            "\1\17",
            "\1\20\1\14\2\uffff\2\20",
            ""
    };

    static final short[] DFA7_eot = DFA.unpackEncodedString(DFA7_eotS);
    static final short[] DFA7_eof = DFA.unpackEncodedString(DFA7_eofS);
    static final char[] DFA7_min = DFA.unpackEncodedStringToUnsignedChars(DFA7_minS);
    static final char[] DFA7_max = DFA.unpackEncodedStringToUnsignedChars(DFA7_maxS);
    static final short[] DFA7_accept = DFA.unpackEncodedString(DFA7_acceptS);
    static final short[] DFA7_special = DFA.unpackEncodedString(DFA7_specialS);
    static final short[][] DFA7_transition;

    static {
        int numStates = DFA7_transitionS.length;
        DFA7_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA7_transition[i] = DFA.unpackEncodedString(DFA7_transitionS[i]);
        }
    }

    class DFA7 extends DFA {

        public DFA7(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 7;
            this.eot = DFA7_eot;
            this.eof = DFA7_eof;
            this.min = DFA7_min;
            this.max = DFA7_max;
            this.accept = DFA7_accept;
            this.special = DFA7_special;
            this.transition = DFA7_transition;
        }
        public String getDescription() {
            return "()* loopback of 114:12: ( AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException )*";
        }
    }
 

    public static final BitSet FOLLOW_jmlCompromisedSpecs_in_jmlSpecifications480 = new BitSet(new long[]{0x0000000000024082L});
    public static final BitSet FOLLOW_jmlGhostSpecs_in_jmlSpecifications482 = new BitSet(new long[]{0x0000000000024082L});
    public static final BitSet FOLLOW_jmlActionSpecs_in_jmlSpecifications486 = new BitSet(new long[]{0x0000000000024082L});
    public static final BitSet FOLLOW_ALSO_in_jmlActionSpecs497 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_ACTION_BEHAVIOR_in_jmlActionSpecs499 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_actClause_in_jmlActionSpecs502 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_ACTION_in_actClause518 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_actionClause_in_actClause523 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_SEMICOLON_in_actClause526 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_jmlMethodCall_in_actionClause534 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_IMPLICATION_in_actionClause536 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_rightSideClause_in_actionClause539 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_rightSideClause551 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_LEFT_in_rightSideClause555 = new BitSet(new long[]{0x0000002840000000L});
    public static final BitSet FOLLOW_rightSideMethodParam_in_rightSideClause558 = new BitSet(new long[]{0x0000002840000000L});
    public static final BitSet FOLLOW_RIGHT_in_rightSideClause562 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_rightSideMethodParam574 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_COMMA_in_rightSideMethodParam577 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_rightSideMethodParam581 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_GHOSTSEQUENCE_in_jmlGhostSpecs594 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_LEFT_in_jmlGhostSpecs596 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_NAME_in_jmlGhostSpecs598 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_EQUAL_in_jmlGhostSpecs600 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_jmlGhostSpecs606 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_RIGHT_in_jmlGhostSpecs609 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_COMPROMISED_BEHAVIOR_in_jmlCompromisedSpecs618 = new BitSet(new long[]{0x0000002000013C02L});
    public static final BitSet FOLLOW_COMMA_in_jmlCompromisedSpecs623 = new BitSet(new long[]{0x0000002000013C02L});
    public static final BitSet FOLLOW_jmlClause_in_jmlCompromisedSpecs627 = new BitSet(new long[]{0x0000002000013C02L});
    public static final BitSet FOLLOW_REQUIRES_in_jmlClause641 = new BitSet(new long[]{0x00000000C4000000L});
    public static final BitSet FOLLOW_ENSURES_in_jmlClause646 = new BitSet(new long[]{0x00000000C4000000L});
    public static final BitSet FOLLOW_ALARMS_in_jmlClause652 = new BitSet(new long[]{0x00000000C4000000L});
    public static final BitSet FOLLOW_SEQUENCE_in_jmlClause658 = new BitSet(new long[]{0x00000000C4000000L});
    public static final BitSet FOLLOW_NOEXCEPTION_in_jmlClause666 = new BitSet(new long[]{0x00000000C4000000L});
    public static final BitSet FOLLOW_jmlCond_in_jmlClause671 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_SEMICOLON_in_jmlClause674 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_AND_in_jmlCond685 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_jmlBinCon_in_jmlCond689 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_jmlMethodCall_in_jmlCond693 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_jmlAlarm_in_jmlCond697 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_jmlException_in_jmlCond701 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_ID_in_jmlBinCon715 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_OPERATOR_in_jmlBinCon719 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_jmlBinCon724 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_jmlMethodCall_in_jmlAlarm736 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_jmlBinCon_in_jmlAlarm740 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_IMPLICATION_in_jmlAlarm743 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_jmlAlarm747 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_methodCall_in_jmlMethodCall758 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_OPERATOR_in_jmlMethodCall762 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_jmlMethodCall767 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_methodCall779 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_LEFT_in_methodCall783 = new BitSet(new long[]{0x0000002840000000L});
    public static final BitSet FOLLOW_methodParam_in_methodCall786 = new BitSet(new long[]{0x0000002840000000L});
    public static final BitSet FOLLOW_RIGHT_in_methodCall790 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_methodParam802 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_COMMA_in_methodParam805 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_ID_in_methodParam809 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_jmlException823 = new BitSet(new long[]{0x0000000000000002L});

}