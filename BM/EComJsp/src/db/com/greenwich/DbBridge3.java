package db.com.greenwich;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import annotation.com.greenwich.compromised_behavior;
import annotation.com.greenwich.ghost_seq;
import shopping.com.greenwich.*;
import static utility.com.greenwich.Uty.*;

public class DbBridge3 {

    @ghost_seq(name = "seq")
    private static int seq;

    private static String databaseURL;

    private static String username;

    private static String password;

    static Connection conn = null;

    static Statement stmt;

    @compromised_behavior(requires = "IsValidServer(_serverName) == 1 && _port > 0 && _port < 65535")
    public static Connection connect(String _serverName, int _port, String _databaseName, String _username, String _password) throws SQLException {
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

    public static Boolean isLogin(String userName, String password, long date) {
        StringBuilder sqlStr = new StringBuilder();
        sqlStr.append("SELECT * FROM users WHERE ");
        sqlStr.append("username='").append(userName).append("'");
        sqlStr.append("AND (password='").append(password).append("')");
        System.out.println(sqlStr);
        try {
            stmt = conn.createStatement();
            ResultSet rset = stmt.executeQuery(sqlStr.toString());
            if (rset.next()) {
                return true;
            }
        } catch (SQLException e) {
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            e.printStackTrace();
        }
        return false;
    }

    @compromised_behavior(alarms = "IsSQLiORAttack(author) ==> SqlInjectionAttack && IsSQLiBlindAttack(author) ==> SqliBlindAttack")
    public static ArrayList<Product> findProducts(String author) {
        ArrayList<Product> products = new ArrayList<Product>();
        StringBuilder sqlStr = new StringBuilder();
        sqlStr.append("SELECT * FROM books WHERE qty > 0 AND ");
        sqlStr.append("author = '").append(author).append("'");
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
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            e.printStackTrace();
        }
        return pd;
    }

    @compromised_behavior(before = "seq > 1", after = "seq ==2")
    public static void updateInventory(int qtyOrdered, int id) throws SQLException {
        assert seq > 1;
        assert seq > 1;
        assert seq > 1;
        assert seq > 1;
        String sqlStr = "UPDATE books SET qty = qty - " + qtyOrdered + " WHERE id = " + id;
        System.out.println(sqlStr);
        stmt = conn.createStatement();
        stmt.executeUpdate(sqlStr);
        seq = 2;
        assert seq == 2;
        seq = 2;
        assert seq == 2;
        seq = 2;
        assert seq == 2;
        seq = 2;
        assert seq == 2;
    }

    public static void insertOrderDetails(int id, int qtyOrdered, Customer customer) throws SQLException {
        String sqlStr = "INSERT INTO order_records values (" + id + ", " + qtyOrdered + ", '" + customer.getName() + "', '" + customer.getEmail() + "', '" + customer.getPhone() + "')";
        System.out.println(sqlStr);
        stmt = conn.createStatement();
        stmt.executeUpdate(sqlStr);
    }
}
