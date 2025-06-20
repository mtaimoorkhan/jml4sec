package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;
import java.util.Arrays;

public class Redirect {
    /*@
    public normal_behavior
      requires true; 
   */
  //@ static_initializer

  static final String[] good_urls = {"https://www.ourwebsite.com/", "https://www.ourwebsite.com/home", "https://www.ourwebsite.com/hello", "https://www.ourwebsite.com/somethingelse", "https://www.google.com/"};
    /*@
    normal_behavior
      requires url != null && good_urls != null; 
      requires (\exists int i; 0 <= i < good_urls.length; good_urls[i] == url); 
      assignable System.out.outputText; 
also
    exceptional_behavior
      requires url == null || good_urls == null; 
      signals (NullPointerException) url == null || good_urls == null; 
      assignable \nothing; 
also
    compromised_behavior
      requires !(\exists int i; 0 <= i < good_urls.length; good_urls[i] == url); 
      alarms INVALID_URL !Arrays.stream(good_urls).anyMatch(url::equals); 
      action INVALID_URL {
        System.err.println("Bad URL: " + url);
        url = "https://www.ourwebsite.com/home";
      }; 
      assignable System.out.outputText; 
   */

  public void DoRedirect(String url) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.Redirect", "", "String", "DoRedirect", new java.lang.Object[]{url, good_urls})) {
      if (url == null || good_urls == null) {
        throw new NullPointerException();
      }
      if (!Arrays.stream(good_urls).anyMatch(url::equals)) {
        System.err.println("Bad URL: " + url);
        url = "https://www.ourwebsite.com/home";
      }
    }
    System.out.println("Redirecting too: " + url);
  }
  
  public static void main(String[] args) {
    Redirect some_webserver = new Redirect();
    some_webserver.DoRedirect("https://www.ourwebsite.com/hello");
    some_webserver.DoRedirect("https://www.ourwebsite.com/home");
    some_webserver.DoRedirect("https://www.google.com/");
    some_webserver.DoRedirect("https://www.somebadwebsite.com/");
    some_webserver.DoRedirect(null);
  }
}