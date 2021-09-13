package shopping.com.greenwich;

import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLException;
import java.util.ArrayList;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import db.com.greenwich.DbBridge;
import utility.com.greenwich.Uty;

public class JBookShop {

    // @ghost int controlSequence=0;
    // requires controlSequence==0;
    // ensures   \result==true -> controlSequence==1 &&
    // \result==false -> controlSequence==0;
    // 
    /*@
	also action_behavior
	 action Uty.IsSQLiORAttack(password) < 1 ==> Uty.redirect(response, "malacious.jsp");
	 action Uty.IsSQLiORAttack(password) < 1 ==> Uty.email("SQLAttack","ijaz.uma@gmail.com");
	 
*/
    public static Boolean isLogin(String userName, String password, HttpServletRequest request, HttpServletResponse response) throws SQLException, ServletException {
        if (Uty.IsSQLiORAttack(password) < 1)
            Uty.email("SQLAttack", "ijaz.uma@gmail.com");
        if (Uty.IsSQLiORAttack(password) < 1)
            Uty.redirect(response, "malacious.jsp");
        if (DbBridge.connect("localhost", 3306, "ebookshop", userName, password) != null)
            if (DbBridge.isLogin(userName, password)) {
                // request.login("root", "zxcvbnm0!");
                request.getSession().setAttribute("user", userName);
                // @set controlSequence = 1;
                return true;
            }
        // @set controlSequence = 0;
        return false;
    }

    /*@ requires controlSequence==1 ||controlSequence==3 ;        
@ 	ensures  controlSequence==2;
@*/
    public static void searchProducts(HttpServletRequest request, HttpServletResponse response) throws IOException, InterruptedException {
        String book_id = request.getParameter("book_id");
        String author_name = request.getParameter("author_name");
        ArrayList<Product> products = null;
        if (!author_name.isEmpty())
            products = DbBridge.findProducts(author_name);
        else if (!book_id.isEmpty())
            products = DbBridge.findProductsByID(book_id);
        PrintWriter out;
        out = response.getWriter();
        HTMLCoder.createStoreWebPage(response, products, out);
        // @set controlSequence = 2;
    }

    /*@ compromised_behavior 
    requires request !=null;
    alarms request.getServerPort() < 0 ==> INVALIDPORT;
 */
    public static void addToCart(HttpServletRequest request, HttpServletResponse response, HttpSession session) throws IOException {
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        assert (request != null);
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", " NA", "NA");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        if (request.getServerPort() < 0)
            Uty.addAttckDetails("addToCart", "INVALIDPORT", "request.getServerPort() < 0", "", "");
        assert (request.getServerPort() < 0) : "INVALIDPORT";
        // @set controlSequence = 3;
        System.out.println("Server Request Port " + request.getServerPort());
        System.out.println("Server Auth Type " + request.getAuthType());
        System.out.println("Request from Path :" + request.getPathInfo());
        System.out.println("Request from Userr" + request.getSession().getAttribute("user").toString());
        System.out.println(request.getContentLength());
        String[] ids = request.getParameterValues("id");
        PrintWriter out = response.getWriter();
        if (ids == null) {
            out.println("<h3>Please Select a Book!</h3></body></html>");
            return;
        }
        // HttpSession session = request.getSession(true);
        Cart cart;
        synchronized (session) {
            // synchronized to prevent concurrent updates
            // Retrieve the shopping cart for this session, if any. Otherwise, create one.
            cart = (Cart) session.getAttribute("cart");
            if (cart == null) {
                // No cart, create one.
                cart = new Cart();
                // Save it into session
                session.setAttribute("cart", cart);
            }
        }
        for (String id : ids) {
            Product pd = DbBridge.findBook(id);
            // Get quantity ordered - no error check!
            int qtyOrdered = Integer.parseInt(request.getParameter("qty" + id));
            int idInt = Integer.parseInt(id);
            cart.add(idInt, pd.getTitle(), pd.getAuthor(), pd.getPrice(), qtyOrdered);
            HTMLCoder.generateCart(out, cart);
            /*
         String todo = request.getParameter("todo");
        if (todo.equals("add")) {
            cart.add(idInt, pd.getTitle(), pd.getAuthor(), pd.getPrice(), qtyOrdered);
        } else if (todo.equals("update")) {
            cart.update(idInt, qtyOrdered);
         }*/
        }
    }

    /*@
  compromised_behavior
  alarms Uty.IsAllowedUrl(page) < 1 ==> MalciousUrl;
*/
    public static void redirectToPage(HttpServletResponse response, String Location, String page) {
        if (Uty.IsAllowedUrl(page) < 1)
            Uty.addAttckDetails("redirectToPage", "MalciousUrl", "Uty.IsAllowedUrl(page) < 1", "page", page);
        if (Uty.IsAllowedUrl(page) < 1)
            Uty.addAttckDetails("redirectToPage", "MalciousUrl", "Uty.IsAllowedUrl(page) < 1", "page", page);
        response.setHeader(Location, page);
    }

    /*@ requires controlSequence == 3;
 @  ensures controlSequence == 4;
@*/
    public static void checkout(HttpServletRequest request, HttpServletResponse response, HttpSession session) throws IOException, SQLException {
        // @set controlSequence = 5;
        Cart cart = null;
        PrintWriter out = response.getWriter();
        String custName = request.getParameter("cust_name");
        // boolean hasCustName = custName != null && ((custName = custName.trim()).length() > 0);
        String custEmail = request.getParameter("cust_email").trim();
        // boolean hasCustEmail = custEmail != null && ((custEmail = custEmail.trim()).length() > 0);
        String custPhone = request.getParameter("cust_phone").trim();
        // boolean hasCustPhone = custPhone != null && ((custPhone = custPhone.trim()).length() > 0);
        Customer customer = new Customer(custName, custEmail, custPhone);
        HTMLCoder.generateUserDetails(out, customer);
        // Retrieve the Cart
        session = request.getSession(false);
        if (session == null) {
            out.println("<h3>Your Shopping cart is empty!</h3></body></html>");
            return;
        }
        synchronized (session) {
            cart = (Cart) session.getAttribute("cart");
            if (cart == null) {
                out.println("<h3>Your Shopping cart is empty!</h3></body></html>");
                return;
            }
            HTMLCoder.generateCheckoutCart(out, cart, customer);
        }
    }
}
