grammar JML;
options {
  language = Java;
}
@header {
package greenwich.ensuresec.jmlgrammar;
import greenwich.ensuresec.structure.JMLStore;
}
@lexer::header {
package greenwich.ensuresec.jmlgrammar;
}

/* LEXER RULES*/
JMLSTART:          '/*@';
JMLEND:            '@*/';
PUBLIC_NORMAL_BEHAVIOR: 'public normal_behavior';

COMPROMISED_BEHAVIOR: 'compromised_behavior';
ACTION_BEHAVIOR:     'action_behavior';

AT: '@';
REQUIRES:        'requires';
ENSURES:         'ensures';
ALARMS: 			 'alarms';
NOEXCEPTION:      'noException';
GHOSTSEQUENCE:    '@ghost_seq';
NAME :			  'name';
SEQUENCE:         'before'|'after';
ALSO: 			  'also';
LOG:				 'log';
MESSAGE:			 'message';
INVALIDATE:		 'invalidate';
LOGOUT:			 'logout';
REDIRECT:		'redirect';
NOTIFY:			'notify';
EMAIL: 			'email';
ACTION: 			'action';


SEMICOLON:      ';';
IMPLICATION: 	'==>';
DOT:             '.';

OPERATOR:       '=='|'!='|'>='|'<='|'>'| '<';
ID:             ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'-'|'.'|'@'|'"')*;

AND: 			'&&';
LINEFEED: 		'\r\n';
//NUMBERS:        ('0'..'9')*;
WS:              (' '|'\t'|'\n'|'\r'|'\f')+        {$channel=HIDDEN;};

 
LEFT: 			'(';
RIGHT: 			')';
EQUAL: 			'=';
COMMA: 			',';


//@ghost_seq(name="seq") 
////////////////////// START OF JML GRAMMAR////////////////////

//@compromised_behavior( requires="a > 1020 && Islogin (x , y)>115",ensures=" b > 10", 
//alarms= "x > y ==>SQLINJECTION")
// noException "true";
//also action_behavior
//	 log "IsSQLiORAttack(password) < 1 ==> file (a.txt)"
//log "IsSQLiORAttack(password) < 1 ==> message (This is attack, a.txt)

//logout "IsSQLiORAttack(password) < 1 ==> invalidate(Session)"
//redirect "IsSQLiORAttack(password) < 1 ==> redirect(www.google.com)";
// notify "IsSQLiORAttack(password) < 1 ==> email(Inj, a@hotmail.com)";	

jmlSpecifications: (jmlCompromisedSpecs|jmlGhostSpecs | jmlActionSpecs)*
;


jmlActionSpecs: ALSO ACTION_BEHAVIOR (actClause) *
;

actClause: (clause = ACTION) {
	JMLStore.setClauseType($clause.text);
	System.out.println("Parsed Clause: "+$clause.text);
} actionClause  SEMICOLON
;

actionClause: jmlMethodCall IMPLICATION (rightSideClause )
;

rightSideClause: mName=ID {JMLStore.addRightSideMethCall($mName.text);} LEFT (rightSideMethodParam)* RIGHT{
}
;

rightSideMethodParam: (pName=ID |COMMA pName=ID ){
	JMLStore.addRightSideMethCallParameter($pName.text);
	System.out.println("param: "+$pName.text);
}
;



jmlGhostSpecs: GHOSTSEQUENCE LEFT NAME EQUAL  var= ID  RIGHT {
	System.out.println("The variable name is " + $var.text );
	JMLStore.setGhostName($var.text);
}
;
jmlCompromisedSpecs: COMPROMISED_BEHAVIOR   (COMMA | jmlClause)* 
;

jmlClause: (clause=REQUIRES| clause=ENSURES | clause=ALARMS | clause=SEQUENCE | clause = NOEXCEPTION) { 
	JMLStore.setClauseType($clause.text);System.out.println("Parsed Clause: "+$clause.text);
	} jmlCond  SEMICOLON
;

jmlCond:   (AND | jmlBinCon | jmlMethodCall | jmlAlarm | jmlException)*  
;

jmlBinCon: leftOp=ID con=OPERATOR rightOp= ID{

	JMLStore.addBinaryCon($leftOp.text,$con.text,$rightOp.text);	
	System.out.println("Binary con added: "+ $con.text);
}
;



jmlAlarm: (jmlMethodCall | jmlBinCon) IMPLICATION threat=ID {
	
	JMLStore.AddAlarms($threat.text);
	System.out.println("Threat : "+ $threat.text);
}
;


jmlMethodCall: methodCall con=OPERATOR rightOp= ID {
	
	JMLStore.addMethCallCond($con.text,$rightOp.text);
	
}
;

methodCall: mName=ID {JMLStore.addMethCall($mName.text);} LEFT (methodParam)* RIGHT{
}
;

methodParam: (pName=ID |COMMA pName=ID ){
	JMLStore.addMethCallParameter($pName.text);
	System.out.println("param: "+$pName.text);
}
;

jmlException: value= ID { System.out.println("exception-value: "+$value.text); JMLStore.AddException($value.text);  }
;


