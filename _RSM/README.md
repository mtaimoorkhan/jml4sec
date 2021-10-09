# RSM (Runtime Security Monitor)
RSM is an inline monitor that takes JML annotated Java programs as an input, automatically translates the JML specifications into assertions and if statments as shown in the below block diagram. The users of RSM are supposed to manualy specify the Java programs.  At run-time, any violation of an assertion indicates a related unpleasant incident. The RSM logs the detected attacks in an XML file.


<img width="550" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/136646721-6694d4b6-12d5-4fd6-867f-ace2b6af0bb5.png">


<h4> Used Specification Language: </h4>
The RSM uses the extended JML specifications to annotate the security properties of Java programs written to develop an e-commerce application.  The syntax of the provided specifications is given in below figure. The @normal_behavior annotation is used to specify the basic sanitary checks. In contrast, the @compromised_behavior is an extended annotation that can determine a system behaviour against the defined cyber-attack classes.
<h4> </h4>
<img width="550" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/136647147-cc6c5610-6158-4d37-a8cc-912c756cab86.png">

The requires clause of compromised_behavior specification consists of two parts: (a) the left side of -> symbol defines the Boolean expression (condition) represented through jml-spec-expr whereas the right side defines the attack. Similarly, other clauses can be interpreted. The basic difference between requires and alarms clauses is the generated code. Indeed, the Runtime Security Monitor only generates assertions against the requires clause. In contrast, the alarms clause also generates code to document the ongoing attack and the available metadata such as failed condition, module (method) name and time of the attack, etc.  

<h4> A working Example: </h4>
The below Figure presents the extended JML specifications for IsLogin (...) method of class DB, along with automatically instrumented Java code. Upon successful detection of a SQLOrInjection attack, the attack details are logged in an XML file through the method addAttackDetails(...). The first parameter of the method Uty.addAttackDetails() is the module name - a module name consists of class and method name. The second parameter is the type of attack, whereas the third parameter represents the failed condition. The 4th and 5th parameters represent the variable name and data that cause SQL injection attacks.



<img width="733" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136648159-e8f7df62-7c19-4b57-9d30-ce8b2f8594a0.png">

  
# How to use JML4Sec?

The JML4Sec can be executed both through command line and the Eclipse IDE development environment – though we encourage to use with the aid of development environment. Please note, the SecRuntime Monitor is primarily designed to aid programmers in writing safe E-Commerce system. 

Command Line Version
1.	Encode security properties in Java classes by following the mentioned syntax
2.	Run the Jar file of the JML4Sec, i.e. java -jar JML4Sec.jar path-to-project
3.	Step 2 will instrument the code with necessary assertions and code.
4.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html
  
Through Eclipse IDE (preferred)
1.	Encode security properties in Java classes by following the mentioned syntax
2.	Import the JML4Sec.jar.jar file in your project
3.	Call the function SRM.instrumentCode(“path-to-file”) in the main function of your project to instrument the code. The SRM is a static class.
4.	Execute the main function
5.	Step 4 will instrument the code with necessary assertions and code.
6.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html



