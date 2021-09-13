package db.com.greenwich;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import shopping.com.greenwich.*;
import utility.com.greenwich.Uty;

// import static utility.com.greenwich.JMLUtilityFunctions.*;
public class DbBridge {

    private static String databaseURL;

    private static String username;

    private static String password;

    static Connection conn = null;

    static Statement stmt;

    /*@ requires myJml.IsValidServer(serverName) && 
 * 			 port >0 && =< 65535 &&
 * 			 myJml.IsValidDatabaseName(databaseName)&&
 * 			 myJml.IsValidUserName(userName)&&
 * 			 myJml.IsValidPassword(password);
 @ myJml.end_to_end_duration (20);
 @ myJml.useport_only(port);
 @ data_flow(databaseURL >> _serverName,_port,_databaseName);
 @ data_flow(username >> _username);
 @ data_flow(password >> _password);
 @ ensures conn!=null;
@*/
    public static Connection connect(String _serverName, int _port, String _databaseName, String _username, String _password) throws SQLException {
        // databaseURL = "jdbc:mysql://localhost:3306/ebookshop";
        System.out.println("connect");
        databaseURL = "jdbc:mysql://" + _serverName + ":" + _port + "/" + _databaseName;
        username = _username;
        password = _password;
        username = "root";
        password = "zxcvbnm0!";
        conn = DriverManager.getConnection(databaseURL, username, password);
        if (conn != null)
            return conn;
        else
            return null;
    }

    /*@ compromised_behavior
requires password.length() > 3 ==> INCORRECXT;
requires Uty.IsSQLiORAttack(password) > 0 ==> SQLINJECTIONError
alarms Uty.IsSQLiORAttack(password) < 1 ==> SQLINJECTION;
*/
    public static Boolean isLogin(String userName, String password) {
        if (Uty.IsSQLiORAttack(password) < 1)
            Uty.addAttckDetails("isLogin", "SQLINJECTION", "Uty.IsSQLiORAttack(password) < 1", "password", password);
        assert (Uty.IsSQLiORAttack(password) > 0);
        assert (password.length() > 3);
        if (Uty.IsSQLiORAttack(password) < 1)
            Uty.addAttckDetails("isLogin", "SQLINJECTION", "Uty.IsSQLiORAttack(password) < 1", "password", password);
        assert (Uty.IsSQLiORAttack(password) > 0);
        assert (password.length() > 3);
        if (Uty.IsSQLiORAttack(password) < 1)
            Uty.addAttckDetails("isLogin", "SQLINJECTION", "Uty.IsSQLiORAttack(password) < 1", "password", password);
        assert (Uty.IsSQLiORAttack(password) > 0);
        assert (password.length() > 3);
        StringBuilder sqlStr = new StringBuilder();
        sqlStr.append("SELECT * FROM users WHERE ");
        sqlStr.append("username='").append(userName).append("'");
        sqlStr.append("AND (password='").append(password).append("')");
        // sqlStr.append("AND users.username = user_roles.username");
        // for debugging
        System.out.println("From Login: " + sqlStr);
        try {
            stmt = conn.createStatement();
            ResultSet rset = stmt.executeQuery(sqlStr.toString());
            if (rset.next()) {
                // empty ResultSet
                return true;
            }
        } catch (SQLException e) {
            System.exit(1);
            e.printStackTrace();
        }
        return false;
    }

    /*@ requires  !myJml.IsSqlInjectionAttack(author);
 @ myJml.end_to_end_duration (20);
 @ myJml.useport_only(port);
@*/
    public static ArrayList<Product> findProducts(String author) {
        ArrayList<Product> products = new ArrayList<Product>();
        // more efficient than String
        StringBuilder sqlStr = new StringBuilder();
        sqlStr.append("SELECT * FROM books WHERE qty > 0 AND (");
        sqlStr.append("author = '").append(author).append("')");
        System.out.println(sqlStr);
        try {
            stmt = conn.createStatement();
            ResultSet rset = stmt.executeQuery(sqlStr.toString());
            while (rset.next()) {
                Product pd = new Product();
                pd.setId(Integer.parseInt(rset.getString("id")));
                pd.setAuthor(rset.getString("author"));
                pd.setTitle(rset.getString("title"));
                pd.setPrice(Float.parseFloat(rset.getString("price")));
                products.add(pd);
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return products;
    }

    public static Product findBook(String id) {
        String sqlStr = "SELECT * FROM books WHERE id = " + id;
        System.out.println(sqlStr);
        Product pd = new Product();
        try {
            stmt = conn.createStatement();
            ResultSet rset = stmt.executeQuery(sqlStr.toString());
            while (rset.next()) {
                pd.setId(Integer.parseInt(rset.getString("id")));
                pd.setAuthor(rset.getString("author"));
                pd.setTitle(rset.getString("title"));
                pd.setPrice(Float.parseFloat(rset.getString("price")));
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return pd;
    }

    public static void updateInventory(int qtyOrdered, int id) throws SQLException {
        String sqlStr = "UPDATE books SET qty = qty - " + qtyOrdered + " WHERE id = " + id;
        doTransaction(sqlStr,"RecTransaction");
    }

    public static void insertOrderDetails(int id, int qtyOrdered, String name, String email, String phone) throws SQLException {
        String sqlStr = "INSERT INTO order_records values (" + id + ", " + qtyOrdered + ", '" + name + "', '" + email + "', '" + phone + "')";
        // for debugging
        String transactionName= "RecTransaction";
        doTransaction(sqlStr,transactionName);
    }

	private static void doTransaction(String sqlQuery, String TransactionName) throws SQLException {
	
		System.out.println(sqlQuery);
        stmt = conn.createStatement();
        stmt.executeUpdate(sqlQuery);
	}

    /*@ compromised_behavior
    alarms Uty.IsSQLiUnionAttack(book_id) < 1 ==> SQLINJECTION; 
    requires password.length() < 5 ==> INCORRECXT;
*/
    public static ArrayList<Product> findProductsByID(String book_id) {
        assert (password.length() < 5);
        if (Uty.IsSQLiUnionAttack(book_id) < 1)
            Uty.addAttckDetails("findProductsByID", "SQLINJECTION", "Uty.IsSQLiUnionAttack(book_id) < 1", "book_id", book_id);
        assert (password.length() < 5);
        if (Uty.IsSQLiUnionAttack(book_id) < 1)
            Uty.addAttckDetails("findProductsByID", "SQLINJECTION", "Uty.IsSQLiUnionAttack(book_id) < 1", "book_id", book_id);
        assert (password.length() < 5);
        if (Uty.IsSQLiUnionAttack(book_id) < 1)
            Uty.addAttckDetails("findProductsByID", "SQLINJECTION", "Uty.IsSQLiUnionAttack(book_id) < 1", "book_id", book_id);
        assert (password.length() < 5);
        if (Uty.IsSQLiUnionAttack(book_id) < 1)
            Uty.addAttckDetails("findProductsByID", "SQLINJECTION", "Uty.IsSQLiUnionAttack(book_id) < 1", "book_id", book_id);
        assert (Uty.IsSQLiUnionAttack(book_id) < 1) : "SQLINJECTION";
        Product pd = findBook(book_id);
        ArrayList<Product> products = new ArrayList<Product>();
        products.add(pd);
        return products;
    }
}
