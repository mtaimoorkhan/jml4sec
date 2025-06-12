package uk.gre.ac.openjmlsec.testclasses;

public class ControlFlowTest {

    //@ public ghost int x = -1;

    public boolean login(String uName, String password) {
        //@ set x = 1;
        return true;
    }
    
   
    /*@ normal_behavior
      @ requires x == 1;
     */
    public boolean isShopItem(int i) {
        return true;
    }
    
    public boolean logOut(String uName) {
        //@ set x = -1;
        return true;
    }
    
    public void callShop() {
        login("ma", "ka");
        isShopItem(1);
        logOut("ma");
        isShopItem(1);
    }
    
    public static void main(String[] args) {
        new ControlFlowTest().callShop();
    }
    
}
