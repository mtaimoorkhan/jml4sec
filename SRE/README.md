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

<h4> Used Specifiucation Language </h4>

<img width="650" alt="Screen Shot 2021-10-09 at 12 08 29 PM" src="https://user-images.githubusercontent.com/1769347/136649597-6a36ec03-0469-4afc-a193-ebe5f022401f.png">

