package shopping.com.greenwich;

import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLException;
import java.util.ArrayList;
import javax.servlet.http.HttpServletResponse;
import db.com.greenwich.DbBridge;

public class HTMLCoder {

    public static void createStoreWebPage(HttpServletResponse response, ArrayList<Product> products, PrintWriter out) throws IOException {
        generateTableHeader(response);
        for (Product pd : products) {
            int id = pd.getId();
            out.println("<tr>");
            out.println("<td><input type='checkbox' name='id' value='" + pd.getId() + "' /></td>");
            out.println("<td>" + pd.getAuthor() + "</td>");
            out.println("<td>" + pd.getTitle() + "</td>");
            out.println("<td>$" + pd.getPrice() + "</td>");
            out.println("<td><input type='text' size='3' value='1' name='qty" + id + "' /></td>");
            out.println("</tr>");
        }
        out.println("</table>");
        out.println("<input type='hidden' name='mname' value='okll' />");
        out.println("<input type='submit' value='Add to My Shopping Cart' />");
        out.println("</form>");
    }

    public static void generateTableHeader(HttpServletResponse response) throws IOException {
        PrintWriter out = response.getWriter();
        out.println("<h2>Query Results</h2>");
        out.println("<form method='get' action='cart.jsp'>");
        out.println("<input type='hidden' name='todo' value='add1' />");
        out.println("<table border='1' cellpadding='6'>");
        out.println("<tr>");
        out.println("<th>&nbsp;</th>");
        out.println("<th>AUTHOR</th>");
        out.println("<th>TITLE</th>");
        out.println("<th>PRICE</th>");
        out.println("<th>QTY</th>");
        out.println("</tr>");
    }

    public static void generateCart(PrintWriter out, Cart cart) {
        // All cases - Always display the shopping cart
        out.println("<h2>My Cart</h2>");
        if (cart.isEmpty()) {
            out.println("<p>Your shopping cart is empty</p>");
        } else {
            out.println("<table border='1' cellpadding='6'>");
            out.println("<tr>");
            out.println("<th>AUTHOR</th>");
            out.println("<th>TITLE</th>");
            out.println("<th>PRICE</th>");
            out.println("<th>QTY</th>");
            out.println("<th>REMOVE</th></tr>");
            float totalPrice = 0f;
            for (Product item : cart.getItems()) {
                int id = item.getId();
                String author = item.getAuthor();
                String title = item.getTitle();
                float price = item.getPrice();
                int qtyOrdered = item.getQtyOrdered();
                out.println("<tr>");
                out.println("<td>" + author + "</td>");
                out.println("<td>" + title + "</td>");
                out.println("<td>" + price + "</td>");
                out.println("<td><form method='get'>");
                out.println("<input type='hidden' name='todo' value='update' />");
                out.println("<input type='hidden' name='id' value='" + id + "' />");
                out.println("<input type='text' size='3' name='qty" + id + "' value='" + qtyOrdered + "' />");
                out.println("<input type='submit' value='Update' />");
                out.println("</form></td>");
                out.println("<td><form method='get'>");
                out.println("<input type='submit' value='Remove'>");
                out.println("<input type='hidden' name='todo' value='remove'");
                out.println("<input type='hidden' name='id' value='" + id + "'>");
                out.println("</form></td>");
                out.println("</tr>");
                totalPrice += price * qtyOrdered;
            }
            out.println("<tr><td colspan='5' align='right'>Total Price: $");
            out.printf("%.2f</td></tr>", totalPrice);
            out.println("</table>");
        }
        out.println("<p><a href='bookstore.jsp'>Select More Books...</a></p>");
    }

    // @ data_flow(totalPrice >> price);
    // @ data_flow(totalPrice >> qtyOrdered);
    public static void generateCheckoutCart(PrintWriter out, Cart cart, Customer customer) throws SQLException {
        // All cases - Always display the shopping cart
        out.println("<h2>My Cart</h2>");
        if (cart.isEmpty()) {
            out.println("<p>Your shopping cart is empty</p>");
        } else {
            out.println("<table border='1' cellpadding='6'>");
            out.println("<tr>");
            out.println("<th>AUTHOR</th>");
            out.println("<th>TITLE</th>");
            out.println("<th>PRICE</th>");
            out.println("<th>QTY</th>");
            out.println("</tr>");
            float totalPrice = 0f;
            for (Product item : cart.getItems()) {
                int id = item.getId();
                String author = item.getAuthor();
                String title = item.getTitle();
                float price = item.getPrice();
                int qtyOrdered = item.getQtyOrdered();
                DbBridge.updateInventory(qtyOrdered, id);
                DbBridge.insertOrderDetails(id, qtyOrdered, customer.getName(), customer.getEmail(), customer.getPhone());
                out.println("<tr>");
                out.println("<td>" + author + "</td>");
                out.println("<td>" + title + "</td>");
                out.println("<td>" + price + "</td>");
                out.println("<td>" + qtyOrdered + "</td>");
                out.println("</tr>");
                totalPrice += price * qtyOrdered;
            }
            out.println("<tr><td colspan='5' align='right'>Total Price: $");
            out.printf("%.2f</td></tr>", totalPrice);
            out.println("</table>");
        }
        out.println("<p><a href='bookstore.jsp'>Select More Books...</a></p>");
    }

    public static void generateUserDetails(PrintWriter out, Customer customer) {
        // Display the name, email and phone (arranged in a table)
        out.println("<h2> Customer Details</h2>");
        out.println("<table>");
        out.println("<tr>");
        out.println("<td>Customer Name:</td>");
        out.println("<td>" + customer.getName() + "</td></tr>");
        out.println("<tr>");
        out.println("<td>Customer Email:</td>");
        out.println("<td>" + customer.getEmail() + "</td></tr>");
        out.println("<tr>");
        out.println("<td>Customer Phone Number:</td>");
        out.println("<td>" + customer.getPhone() + "</td></tr>");
        out.println("</table>");
    }
}
