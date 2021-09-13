# jml4sec
Jml4Sec consists of two main modules : (a) Behavioural Detection Monitor (b) Behavioural Recovery Monitor. The former detects cyber attacks, particularly attacks through SQLi and HTTP Servlets objects whereas the later provides mechanism to recover from the occured cyber attack. Bascially the programmer is supposed to specify the detection and recovery actions through extended JML specifications.  The syntax of the extended JML specifications is provided in below figure. 

<img width="569" alt="Screen Shot 2021-09-13 at 3 47 10 PM" src="https://user-images.githubusercontent.com/1769347/133070884-abf2ee99-e492-4b84-9c12-00d57b47b1af.png">



JML4Sec takes JML annotated Java programs as an input, automatically translates the JML specifications into detection and recovery code. Basically, JML4Sec syntactically translates specifications into assertions, code-gaurd through if and code related with recovery action. The below figure provides the block diagram of JML4Sec.
<img width="681" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/133071534-aaa38d82-5fc1-433a-bbf2-9f53eb76b191.png">

The below figure provides the detection and recovery specifications for a method named "addtoCart".

<img width="518" alt="Screen Shot 2021-09-13 at 4 05 21 PM" src="https://user-images.githubusercontent.com/1769347/133073092-922b6784-930c-47af-96c2-a9564b4c2b35.png">

  

![image](https://user-images.githubusercontent.com/1769347/133073238-a39788ab-5798-4f53-bff1-4022dfb94445.png)


# How to use jml4Sec?

The JML4Sec can be executed both through command line and the Eclipse IDE development environment – though we encourage to use with the aid of development environment. Please note, the SecRuntime Monitor is primarily designed to aid programmers in writing safe E-Commerce system. 

4.2.1.	Command Line Version
1.	Encode security properties in Java classes by following the mentioned syntax
2.	Run the Jar file of the JML4Sec, i.e. java -jar JML4Sec.jar path-to-project
3.	Step 2 will instrument the code with necessary assertions and code.
4.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html
  
4.2.2.	Through Eclipse IDE (preferred)
1.	Encode security properties in Java classes by following the mentioned syntax
2.	Import the JML4Sec.jar.jar file in your project
3.	Call the function SRM.instrumentCode(“path-to-file”) in the main function of your project to instrument the code. The SRM is a static class.
4.	Execute the main function
5.	Step 4 will instrument the code with necessary assertions and code.
6.	Enable JVM assertion before executing E-commerce application - https://tutoringcenter.cs.usfca.edu/resources/enabling-assertions-in-eclipse.html


