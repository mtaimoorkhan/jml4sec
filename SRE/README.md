# SRE (Software Recovery Engine)
The SRE proposes a specification-based approach to recover from the cyber-attacks as shown in below figure. The SRE works in collusion with RSM (Runtime Security Monitor). The SRE defines three approaches to recover from cyber-attacks: (a) Full Recovery (b) Partial Recovery (c) No Recovery. The first approach presents specifications to encode full recovery from the attacks, whereas the second approach provides partial recovery. The third approach provides no recovery to the occurred attack(s). 

<img width="650" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136649360-1201952a-9269-422e-b9c8-a24a162c83dd.png">

The key features of SRE are listed below:

**Logout:** On successful detection of a SQLi attack, the SRE proposes to logout the user from the system. 

**Block a User:** The SRE specifications provide a mechanism to block a user, in case he/she attempts to launch an attack on system. The SRE may log the details of a malicious user in an XML file and block the user temporarily.

**Block IP address:** On successful detection of any type of cyber-attack, the SRE may log the IP address in an XML file – thus preventing a malicious user from accessing the E-Commerce System, again from the same IP address.

**Redirect:** The programmer may specify to redirect the system to a specific web page, in case the detection of a cyber-attack.

**Notify to Admin:** The programmer may specify the email address of the E-Commerce System administrator. The generated code will send the email to the provided email address, along with available data to inform the administrator about the attack.

**Nullify Object:** In case of corrupting data of a Marshalled object, the programmer may nullify the object to avoid further damage to the system.

**Rollback a Transaction:** The SRE provides a mechanism to programmer to rollback a malicious transaction, in case of a SQLi attack. 

<h2>Used Specifiucation Language </h2>

The SRE uses the extended JML specifications to annotate the security and recovery properties of Java programs as shown in below Figure. The @normal_behavior annotation is used to specify the basic sanitary checks, @compromised_behavior is used to specify attack detection and @action_behavior is used to specify the recovery (action).  

<img width="400" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136649597-6a36ec03-0469-4afc-a193-ebe5f022401f.png">

<h2> A Working Example</h2>

The below figure presents the (extended) JML specifications for the method IsLoginMethod (...). The specifications written inside @normal_behavior represent the basic sanctity checks, whereas the specifications for the @action_behavior ensure two things: (a) It informs system administrator through email, i.e., admin@gmail.com, that an attacker launched an SQLi attack on the e-commerce application. (b) It redirects the attacker to another web page, i.e., “malicious.jsp” – The web page's contents advise the user to stop attacking the system. Please note that we strictly follow the JML policy and only use Pure methods in the specifications – a pure method is a method that does not have any side-effect.  In the below specifications, IsSqliORAttack, redirect, and email is pure methods defined in the static class Uty (Utility). 

<img width="550" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136649905-8e49e438-6aa4-48d3-a6cc-1b180ed5342f.png">

<h2> How to use SRE? </h2>

The SRE can be executed both through command line and the Eclipse IDE development environment – though we encourage to use with the aid of development environment. Please note, the SRE is primarily designed to aid programmers in writing safe E-Commerce system. 

Command Line Version
1.	Encode security and recovery properties in Java classes by following the mentioned syntax
2.	Run the Jar file of the SRE, i.e. java -jar SRE.jar path-to-project
3.	Step 2 will instrument the code with necessary assertions and code.
4.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html
  
Through Eclipse IDE (preferred)
1.	Encode security and recovery properties in Java classes by following the mentioned syntax
2.	Import the SRE.jar file in your project
3.	Call the function SRM.instrumentCode(“path-to-file”) in the main function of your project to instrument the code. The SRM is a static class.
4.	Execute the main function
5.	Step 4 will instrument the code with necessary assertions and code.
6.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html






