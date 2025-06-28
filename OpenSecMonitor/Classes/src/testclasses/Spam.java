package testclasses;

public class Spam{

	static final long BLOCK_OUT = 10L; //<< this has to be big in testing because Z3 is slow
	long last_call = 0;
	long prev_call = BLOCK_OUT + 1;
	
	//@ private normal_behavior
		//@ requires prev_call > BLOCK_OUT + last_call;
		//@ modifies prev_call, last_call, System.time, System.nexttime;
	//@ private compromised_behavior
		//@ requires prev_call <= BLOCK_OUT + last_call;
		//@ modifies prev_call, last_call, System.time, System.nexttime;
		//@ alarms SPAM prev_call <= BLOCK_OUT + last_call;
		/*@ action SPAM {
			System.err.println("Too many pings within time frame, aborting");
			prev_call = System.currentTimeMillis() / 1000l;
			return;
		};*/
	
	void Ping() {
		last_call = prev_call;
		prev_call = System.currentTimeMillis() / 1000l;
		
		//Simulate something happening...
		try {
			Thread.sleep(10);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
    public static void main(String[] args) {
    	Spam spam = new Spam();
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    	spam.Ping();
    }
}
