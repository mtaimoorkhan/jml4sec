package testclasses;
import java.util.Arrays;

public class Redirect {
	//@ public normal_behavior
	//@ requires true;
	//@ static_initializer
	static final String[] good_urls = {
		"https://www.ourwebsite.com/",
		"https://www.ourwebsite.com/home",
		"https://www.ourwebsite.com/hello",
		"https://www.ourwebsite.com/sorry",
		"https://www.ourwebsite.com/somethingelse",
		//.....
		"https://www.google.com/",
	};
	
	//@ normal_behavior
		//@ requires url != null && good_urls != null;
		//@ requires (\exists int i; 0 <= i < good_urls.length; good_urls[i] == url);
		//@ modifies System.out.outputText;
	//@ also exceptional_behavior
		//@ requires url == null || good_urls == null;
		//@ signals (NullPointerException) url == null || good_urls == null;
		//@ modifies \nothing;
	//@ also compromised_behavior
		//@ requires !(\exists int i; 0 <= i < good_urls.length; good_urls[i] == url);
		//@ alarms INVALID_URL !Arrays.stream(good_urls).anyMatch(url::equals);
		/*@ action INVALID_URL {
			System.err.println("Bad URL: " + url); 
			//Redirect to home
			url = "https://www.ourwebsite.com/sorry";
		};*/
		//@ modifies System.out.outputText;
	public void DoRedirect(String url) {
		//Do the redirect
		//...
		//Something like this
		//response.sendRedirect(...);
		//...
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
