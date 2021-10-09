# RSM (Runtime Security Monitor)

The RSM is a specification-based security behavioral monitor. The user of RSM is supposed to add JML styled security specifications into Java classes. The RSM generates assertions and guards (if statement) to avoid cyber-attacks as shown in below diagram. The main features of RSM are listed below:

<h4> Avoiding Attacks through SQL Injection: <h4>
The programmer may add necessary security specifications to avoid different types of SQL injections attacks, notably In-Band SQLi, Error-Based SQLi and Inferential SQLi attacks. The presence of these types of attacks may corrupt the database, violate database integrity and
allow unauthorized access to database.


<h4> Avoiding Attacks through HTTPServlet Objects: </h4>
HTTPServlet Objects are widely used to encode a web-based e-commerce application. Attackers may launch an attack through these objects by initiating a communication through unauthorised port and from an unauthorized IP address. RSM provides a way to avoid these types of attacks through automatically generated assertions.

<h4> Avoiding Buffer Overflow: </h4>
RSM provides a way to handle buffer overflow attacks, initiated through a user input. The programmer may add necessary specifications to avoid overflowing a memory buffer by specifying the value ranges.  .

<h4> Altering Control Flow: </h4>
Attackers may launch an attack by altering the execution flow (method control flow) of an object. RSM provides a way to encode control-flow information in a method specification, hence provides a sound deterrence against control flow attacks.

<h4> Perform Sanity Checks: </h4>
The RSM performs different types of sanity checks such as to check object nullness, to ensure the range of integer values and to validate the legality of Date object. Furthermore, these sanity checks can be elegantly designed to properly unmarshall an object in Java.

<h4> Log Attacks Details: </h4>
The RSM does not allow to occur above-described attacks, however it logs the attack-attempts in an XML file. This XML file can be used by other ENSURESEC tools to audit and recovery.  




<img width="550" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/136646721-6694d4b6-12d5-4fd6-867f-ace2b6af0bb5.png">


<h2> Used Specification Language: </h2>
The RSM uses the extended JML specifications to annotate the security properties of Java programs written to develop an e-commerce application.  The syntax of the provided specifications is given in below figure. The @normal_behavior annotation is used to specify the basic sanitary checks. In contrast, the @compromised_behavior is an extended annotation that can determine a system behaviour against the defined cyber-attack classes.
<h4> </h4>
<img width="550" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/136647147-cc6c5610-6158-4d37-a8cc-912c756cab86.png">

The requires clause of compromised_behavior specification consists of two parts: (a) the left side of -> symbol defines the Boolean expression (condition) represented through jml-spec-expr whereas the right side defines the attack. Similarly, other clauses can be interpreted. The basic difference between requires and alarms clauses is the generated code. Indeed, the Runtime Security Monitor only generates assertions against the requires clause. In contrast, the alarms clause also generates code to document the ongoing attack and the available metadata such as failed condition, module (method) name and time of the attack, etc.  

<h2> A Working Example: </h2>
The below Figure presents the extended JML specifications for IsLogin (...) method of class DB, along with automatically instrumented Java code. Upon successful detection of a SQLOrInjection attack, the attack details are logged in an XML file through the method addAttackDetails(...). The first parameter of the method Uty.addAttackDetails() is the module name - a module name consists of class and method name. The second parameter is the type of attack, whereas the third parameter represents the failed condition. The 4th and 5th parameters represent the variable name and data that cause SQL injection attacks.



<img width="733" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136648159-e8f7df62-7c19-4b57-9d30-ce8b2f8594a0.png">

<h2> How to use JML4Sec? </h2>

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



