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
AT: '@';
REQUIRES:        'requires';
ENSURES:         'ensures';
ALARMS: 			 'alarms';
GHOSTSEQUENCE:    '@ghost_seq';
NAME :			  'name';
SEQUENCE:         'before'|'after';
COMPROMISED_BEHAVIOR: 'compromised_behavior';

SEMICOLON:      ';';
IMPLICATION: 	'==>';

OPERATOR:       '=='|'!='|'>='|'<='|'>'| '<';
ID:             ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'-')*;
DOT:             '.';
AND: 			'&&';
LINEFEED: 		'\r\n';
//NUMBERS:        ('0'..'9')*;
WS:              (' '|'\t'|'\n'|'\r'|'\f')+        {$channel=HIDDEN;};

 
LEFT: 			'(';
RIGHT: 			')';
QUOTE: 			'"';
EQUAL: 			'=';
COMMA: 			',';


//@ghost_seq(name="seq") 
////////////////////// START OF JML GRAMMAR////////////////////

//@compromised_behavior( requires="a > 1020 && Islogin (x , y)>115",ensures=" b > 10", 
//alarms= "x > y ==>SQLINJECTION")

jmlSpecifications: jmlCompromisedSpecs|jmlGhostSpecs
;

jmlGhostSpecs: GHOSTSEQUENCE LEFT NAME EQUAL QUOTE var= ID QUOTE RIGHT {
	System.out.println("The variable name is " + $var.text );
	JMLStore.setGhostName($var.text);
}
;
jmlCompromisedSpecs: COMPROMISED_BEHAVIOR LEFT  (COMMA | jmlClause)* RIGHT
;

jmlClause: (clause=REQUIRES| clause=ENSURES | clause=ALARMS | clause=SEQUENCE ) EQUAL { JMLStore.setClauseType($clause.text);} jmlCond 
;

jmlCond:  QUOTE (AND | jmlBinCon | jmlMethodCall | jmlAlarm )* QUOTE 
;

jmlBinCon: leftOp=ID con=OPERATOR rightOp= ID{

	JMLStore.addBinaryCon($leftOp.text,$con.text,$rightOp.text);	
	System.out.println("Binary con added: "+ $con.text);
}
;



jmlAlarm: methodCall IMPLICATION threat=ID {
	
	JMLStore.AddAlarms($threat.text);
	System.out.println("Threat : "+ $threat.text);
}
;


jmlMethodCall: methodCall con=OPERATOR rightOp= ID {
	
	JMLStore.addMethCallCond($con.text,$rightOp.text);
	
}
;

methodCall: (qName=ID DOT)? mName=ID {JMLStore.addMethCall($mName.text); JMLStore.addMethQualifiedName($qName.text);} LEFT (methodParam)* RIGHT{
}
;

methodParam: (pName=ID |COMMA pName=ID ){
	JMLStore.addMethCallParameter($pName.text);
	System.out.println("param: "+$pName.text);
}
;


