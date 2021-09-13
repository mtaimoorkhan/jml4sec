# jml4sec
Jml4Sec consists of two main modules : (a) Behavioural Detection Monitor (b) Behavioural Recovery Monitor. The former detects cyber attacks, particularly attacks through SQLi and HTTP Servlets objects whereas the later provides mechanism to recover from the occured cyber attack. Bascially the programmer is supposed to specify the detection and recovery actions through extended JML specifications.  The syntax of the extended JML specifications is provided in below figure. 

<img width="569" alt="Screen Shot 2021-09-13 at 3 47 10 PM" src="https://user-images.githubusercontent.com/1769347/133070884-abf2ee99-e492-4b84-9c12-00d57b47b1af.png">



JML4Sec takes JML annotated Java programs as an input, automatically translates the JML specifications into detection and recovery code. Basically, JML4Sec syntactically translates specifications into assertions, code-gaurd through if and code related with recovery action. The below figure provides the block diagram of JML4Sec.
<img width="681" alt="Screen Shot 2021-09-13 at 3 53 15 PM" src="https://user-images.githubusercontent.com/1769347/133071534-aaa38d82-5fc1-433a-bbf2-9f53eb76b191.png">
  


