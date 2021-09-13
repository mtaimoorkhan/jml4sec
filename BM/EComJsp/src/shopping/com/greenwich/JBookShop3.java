package shopping.com.greenwich;

import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLException;
import java.util.ArrayList;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import annotation.com.greenwich.compromised_behavior;
import db.com.greenwich.DbBridge;

public class JBookShop3 {

    public static Boolean isLogin(String userName, String password, HttpServletRequest request) throws SQLException, ServletException {
        if (DbBridge.connect("localhost", 3306, "ebookshop", userName, password) != null)
            if (DbBridge.isLogin(userName, password)) {
                request.getSession().setAttribute("user", userName);
                return true;
            }
        return false;
    }

    public static void searchProducts(HttpServletRequest request, HttpServletResponse response) throws IOException, InterruptedException {
        String author = request.getParameter("author");
        String author_name = request.getParameter("author_name");
        ArrayList<Product> products;
        if (!author_name.isEmpty())
            products = DbBridge.findProducts(author_name);
        else
            products = DbBridge.findProducts(author);
        PrintWriter out;
        out = response.getWriter();
        HTMLCoder.createStoreWebPage(response, products, out);
    }

    @compromised_behavior(requires = "request.getServerPort()==8082")
    public static void addToCart(HttpServletRequest request, HttpServletResponse response, HttpSession session) throws IOException {
        assert request.getServerPort() == 8082;
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
        Cart cart;
        synchronized (session) {
            cart = (Cart) session.getAttribute("cart");
            if (cart == null) {
                cart = new Cart();
                session.setAttribute("cart", cart);
            }
        }
        for (String id : ids) {
            Product pd = DbBridge.findBook(id);
            int qtyOrdered = Integer.parseInt(request.getParameter("qty" + id));
            int idInt = Integer.parseInt(id);
            cart.add(idInt, pd.getTitle(), pd.getAuthor(), pd.getPrice(), qtyOrdered);
            HTMLCoder.generateCart(out, cart);
        }
    }

    public static void checkout(HttpServletRequest request, HttpServletResponse response, HttpSession session) throws IOException, SQLException {
        Cart cart = null;
        PrintWriter out = response.getWriter();
        String custName = request.getParameter("cust_name");
        String custEmail = request.getParameter("cust_email").trim();
        String custPhone = request.getParameter("cust_phone").trim();
        Customer customer = new Customer(custName, custEmail, custPhone);
        HTMLCoder.generateUserDetails(out, customer);
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
