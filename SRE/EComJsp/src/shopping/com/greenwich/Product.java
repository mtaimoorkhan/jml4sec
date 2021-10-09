package shopping.com.greenwich;

public class Product {

    private int id;

    private String title;

    private String author;

    private float price;

    private int qtyOrdered;

    // Constructor
    public Product(int id, String title, String author, float price, int qtyOrdered) {
        this.id = id;
        this.title = title;
        this.author = author;
        this.price = price;
        this.qtyOrdered = qtyOrdered;
    }

    public Product() {
        // TODO Auto-generated constructor stub
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getAuthor() {
        return author;
    }

    public void setAuthor(String author) {
        this.author = author;
    }

    public float getPrice() {
        return price;
    }

    public void setPrice(float price) {
        this.price = price;
    }

    public int getQtyOrdered() {
        return qtyOrdered;
    }

    public void setQtyOrdered(int qtyOrdered) {
        this.qtyOrdered = qtyOrdered;
    }
}
