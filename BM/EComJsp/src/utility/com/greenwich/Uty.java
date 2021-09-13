package utility.com.greenwich;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.text.SimpleDateFormat;
import java.util.Date;
import javax.servlet.http.*;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/*
import java.util.*;
import javax.mail.*;
import javax.mail.internet.*;
import javax.mail.Session;
import javax.mail.Transport;
*/
public class Uty {

    public static void addAttckDetails(String componenet, String type, String condition, String parameter, String value) {
        System.out.println("addAttckDetails");
        LogAttack.addAttckDetails(componenet, type, condition, parameter, value);
    }

    public static void addAttckDetails(String componenet, String type, String condition, String parameter, int value) {
        // System.out.println("addAttckDetails");
        LogAttack.addAttckDetails(componenet, type, condition, parameter, String.valueOf(value));
    }

    public static int IsSQLiORAttack(String input) {
        // System.out.println("IsSQLiORAttack");
        input = input.toUpperCase();
        if (input.contains(" OR") == true)
            return 0;
        return 1;
    }

    public static int IsRequestFromValidUser(HttpServletRequest request, HttpSession session) {
        return 0;
    }

    public static int IsFilePathOK(String path) {
        return checkPresenceInConfigFile(path, "file_paths", "path");
    }

    public static int IsAllowedUrl(String url) {
        return checkPresenceInConfigFile(url, "allowed_urls", "url");
    }

    private static int checkPresenceInConfigFile(String path, String root, String element) {
        String fileName = "/Users/drijazahmed/runtime-EclipseApplication/EComJsp/WebContent/WEB-INF/config.xml";
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
        Document doc = null;
        try {
            doc = db.parse(fileName);
        } catch (SAXException | IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        NodeList people = doc.getElementsByTagName(root);
        for (int i = 0; i < people.getLength(); i++) {
            Element ele = (Element) people.item(i);
            for (int j = 0; j < ele.getElementsByTagName(element).getLength(); j++) {
                String element_value = ele.getElementsByTagName(element).item(j).getTextContent();
                if (element_value.compareToIgnoreCase(path) == 0) {
                    return 1;
                }
            }
        }
        return 0;
    }

    public static int IsDateValid(long date) {
        if (date < 0)
            return 0;
        else
            return 1;
    }

    public static int IsValidServer(String url) {
        return 1;
    }

    public static int IsValidEcomUrl(String url) {
        return 1;
    }

    public static boolean IsValidPassword(String password) {
        return true;
    }

    public static int IsSQLiUnionAttack(String input) {
        input = input.toUpperCase();
        if (input.contains(" UNION") == true)
            return 0;
        return 1;
    }

    public static boolean IsSQLiBlindAttack(String input) {
        input = input.toUpperCase();
        if (input.contains(" AND") == true)
            return false;
        return true;
    }

    public static boolean IsErrorBasedSQLi(String input) {
        input = input.toUpperCase();
        if (input.contains(" '") == true)
            return false;
        return true;
    }

    public static void invalidate(HttpSession session) {
        session.invalidate();
    }

    public static void message(String msg, String file) {
        // "Inj", "a.txt"
        try (FileWriter fw = new FileWriter(file, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)) {
            SimpleDateFormat formatter = new SimpleDateFormat("dd/MM/yyyy HH:mm:ss");
            Date date = new Date();
            out.println(formatter.format(date) + ": " + msg);
        } catch (IOException e) {
            // exception handling left as an exercise for the reader
        }
        // $(xmlFile).document();
    }

    public static void redirect(HttpServletResponse response, String target) {
        // www.google.com, "httpReq"
        try {
            response.sendRedirect("http://localhost:8080/EComJsp/" + target);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    public static void email(String msg, String recipient) {
        // send("ijaz.uma@gmail.com", "Corrigendum0!", recipient, "Behavioral Monitor", msg);
    }

    /*
    public static void send(String from, String password, String to, String sub, String msg) {
        // Get properties object
        Properties props = new Properties();
        props.put("mail.smtp.host", "smtp.gmail.com");
        props.put("mail.smtp.socketFactory.port", "465");
        props.put("mail.smtp.socketFactory.class", "javax.net.ssl.SSLSocketFactory");
        props.put("mail.smtp.auth", "true");
        props.put("mail.smtp.port", "465");
        // get Session
        Session session = Session.getDefaultInstance(props, new javax.mail.Authenticator() {

            protected PasswordAuthentication getPasswordAuthentication() {
                return new PasswordAuthentication(from, password);
            }
        });
        // compose message
        try {
            MimeMessage message = new MimeMessage(session);
            message.addRecipient(Message.RecipientType.TO, new InternetAddress(to));
            message.setSubject(sub);
            message.setText(msg);
            // send message
            Transport.send(message);
            System.out.println("message sent successfully");
        } catch (MessagingException e) {
            throw new RuntimeException(e);
        }
    }
*/
    public static void marshall() {
        try {
            // creating the JAXB context
            JAXBContext jContext = JAXBContext.newInstance(Student.class);
            // creating the marshaller object
            Marshaller marshallObj = (Marshaller) jContext.createMarshaller();
            // setting the property to show xml format output
            marshallObj.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, true);
            // setting the values in POJO class
            Student student = new Student("abhishek", 1163, "hadoop");
            // calling the marshall method
            marshallObj.marshal(student, new FileOutputStream("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/student.xml"));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public String getNodeValue() {
        Document xmlDocument = null;
        return ((Document) ((Document) xmlDocument.getElementsByTagName("category").item(0)).getElementsByTagName("book").item(0)).getElementsByTagName("title").item(0).getNodeValue();
    }

    public static NodeList getXMLNodes(String meta_data, String fileName) {
        // String fileName= "/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/metadata.xml";
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
        try {
            Document doc = db.parse(fileName);
            NodeList nodes = doc.getElementsByTagName(meta_data);
            // Node node = nodes.item(0);
            // Element eElement = (Element) node;
            // System.out.println(eElement.getElementsByTagName("name").item(0).getTextContent());
            return nodes;
            // doc.getElementsByTagName("student").item(0)).getElementsByTagName("book").item(0)).getElementsByTagName("title").item(0).getNodeValue();
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    public static void unmarshall(String xmlObjStr) {
        try {
            // getting the xml file to read
            File file = new File("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/student.xml");
            // creating the JAXB context
            JAXBContext jContext = JAXBContext.newInstance(Student.class);
            // creating the unmarshall object
            Unmarshaller unmarshallerObj = jContext.createUnmarshaller();
            // calling the unmarshall method
            Student student = (Student) unmarshallerObj.unmarshal(new StreamSource(new StringReader(xmlObjStr.toString())));
            System.out.println(student.getName() + " " + student.getId() + " " + student.getSubject());
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public static int IsDataValidForUnmashalling(String xmlObjStr) {
        String metaDatafile = "/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/metadata.xml";
        String objDatafile = "/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/student.xml";
        NodeList nodes = getXMLNodes("meta_data", metaDatafile);
        boolean isValid = true;
        // System.out.println(nodes.item(0).getNodeValue());
        for (int i = 0; i < nodes.getLength(); i++) {
            Node node = nodes.item(i);
            Element eElement = (Element) node;
            String nameElementValue = eElement.getElementsByTagName("name").item(0).getTextContent();
            String typeElementValue = eElement.getElementsByTagName("type").item(0).getTextContent();
            String minElementValue = eElement.getElementsByTagName("min").item(0).getTextContent();
            String maxElementValue = eElement.getElementsByTagName("max").item(0).getTextContent();
            switch(typeElementValue) {
                case "int":
                    String s_attributeValue = getAttributeValue(objDatafile, nameElementValue);
                    isValid = isValid && isValueWithinRange(minElementValue, maxElementValue, s_attributeValue);
                    break;
                case "two":
                    System.out.println("two");
                    break;
                case "three":
                    System.out.println("three");
                    break;
                default:
                    System.out.println("no match");
            }
            String attributeValue = getAttributeValue(objDatafile, nameElementValue);
            System.out.println(attributeValue);
        }
        if (isValid)
            return 1;
        else
            return 0;
    }

    private static boolean isValueWithinRange(String minElementValue, String maxElementValue, String s_attributeValue) {
        int i_attributeValue = Integer.parseInt(s_attributeValue);
        int i_min = Integer.parseInt(minElementValue);
        int i_max = Integer.parseInt(maxElementValue);
        if (i_attributeValue >= i_min && i_attributeValue <= i_max)
            return true;
        return false;
    }

    private static String getAttributeValue(String objDatafile, String nameElementValue) {
        NodeList objDataNodes = getXMLNodes(nameElementValue, objDatafile);
        Node fieldNode = objDataNodes.item(0);
        Element field = (Element) fieldNode;
        String fieldValue = field.getTextContent();
        return fieldValue;
    }

    public static void logAttack() {
        String fileName = "/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/output.xml";
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
        try {
            Document doc = db.parse(fileName);
            NodeList people = doc.getElementsByTagName("attacks");
            people.item(0).appendChild(createAttack(doc, "DbBridge.IsLogin", "InBand_Sqli", "IsSQLiORAttack(password)", "password", "ad' OR '1=1"));
            people.item(0).appendChild(createAttack(doc, "DbBridge.insertOrderDetails", "UnionBased_Sqli", "IsUnionBasedAttack(name)", "name", "union ..."));
            people.item(0).appendChild(createAttack(doc, "DbBridge.updateInventory", "ErrorBased_Sqli", "IsErrorBasedAttack(qty)", "qty", ";"));
            people.item(0).appendChild(createAttack(doc, "DbBridge.updateInventory", "BufferOverFlow", "IsBufferOverFlow(qty)", "qty", "7898989756498799966"));
            people.item(0).appendChild(createAttack(doc, "DbBridge.updateInventory", "BufferOverFlow", "IsBufferOverFlow(qty)", "qty", "7898989756498799966"));
            people.item(0).appendChild(createAttack(doc, "JBookShop.addToCart", "undefined_port", "assert request.getServerPort() == 8080", "request", "-80"));
            WriteToFile(doc, fileName);
            try {
                System.out.println(nodeToString(doc));
            } catch (TransformerException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    private static String nodeToString(Node node) throws TransformerException {
        StringWriter buf = new StringWriter();
        Transformer xform = TransformerFactory.newInstance().newTransformer();
        xform.transform(new DOMSource(node), new StreamResult(buf));
        return buf.toString();
    }

    private static Element createAttackDetails(Document doc, String name, String value) {
        Element el = doc.createElement(name);
        el.appendChild(doc.createTextNode(value));
        return el;
    }

    private static Element createAttack(Document doc, String componentName, String attackType, String cond, String var, String data) {
        Element el = doc.createElement("attack");
        el.appendChild(createAttackDetails(doc, "component_name", componentName));
        el.appendChild(createAttackDetails(doc, "type", attackType));
        el.appendChild(createAttackDetails(doc, "failed_condition", cond));
        el.appendChild(createAttackDetails(doc, "variable_name", var));
        el.appendChild(createAttackDetails(doc, "corrupted_data", data));
        SimpleDateFormat formatter = new SimpleDateFormat("dd/MM/yyyy HH:mm:ss");
        Date date = new Date();
        el.appendChild(createAttackDetails(doc, "time", formatter.format(date)));
        // Element images = doc.createElement("images");
        // images.appendChild(createPersonDetailElement(doc, "img", image));
        // el.appendChild(images);
        return el;
    }

    public static void WriteToFile(Document doc, String fileName) {
        Transformer transformer = null;
        try {
            transformer = TransformerFactory.newInstance().newTransformer();
        } catch (TransformerConfigurationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (TransformerFactoryConfigurationError e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        StreamResult result = null;
        try {
            result = new StreamResult(new FileWriter(fileName));
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        DOMSource source = new DOMSource(doc);
        try {
            transformer.transform(source, result);
        } catch (TransformerException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
