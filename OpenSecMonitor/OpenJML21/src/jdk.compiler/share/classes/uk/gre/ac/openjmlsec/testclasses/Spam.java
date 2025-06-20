package uk.gre.ac.openjmlsec.testclasses;

public class Spam implements Runnable{

	static int num_pings = 0;
	static int MAX_PINGS = 2;
	
	//@ private normal_behavior
		//@ requires num_pings >= 0 && num_pings < MAX_PINGS;
		//@ modifies num_pings;
	//@ private compromised_behavior
		//@ requires num_pings >= MAX_PINGS;
		//@ modifies num_pings;
		//@ alarms SPAM num_pings >= MAX_PINGS;
		//@ action SPAM {System.err.println("Too many pings, aborting"); return;};
	
	void Ping() {
		num_pings += 1;
		//Simulate something happening...
		try {
			Thread.sleep(40000);
		} catch (Exception e) {
			e.printStackTrace();
		}
		num_pings -= 1;
	}

    public void run() {
    	Ping();
    }
	
    public static void main(String[] args) {
    	Spam spam = new Spam();
		//*
	    try {
	    	//Send requests
			new Thread(spam).start();
			Thread.sleep(3000);
			new Thread(spam).start();
		    Thread.sleep(3000);
			new Thread(spam).start();
		    Thread.sleep(3000);
			new Thread(spam).start();
		    Thread.sleep(3000);
			new Thread(spam).start();
		    Thread.sleep(3000);
			new Thread(spam).start();
		    Thread.sleep(3000);
			new Thread(spam).start();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		/*/
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    	//*/
    }
}
