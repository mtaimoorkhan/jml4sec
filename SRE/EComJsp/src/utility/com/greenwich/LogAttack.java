package utility.com.greenwich;

import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.text.SimpleDateFormat;
import java.util.Date;
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
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class LogAttack {

    public static void addAttckDetails(String componenet, String type, String condition, String parameter, String value) {
        printAttackDetails(componenet, type, condition, parameter, value);
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
            people.item(0).appendChild(createAttack(doc, componenet, type, condition, parameter, value));
            WriteToFile(doc, fileName);
            /*		
			try { System.out.println(nodeToString(doc));}
			 catch (TransformerException e) {e.printStackTrace();}
		*/
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    private static void printAttackDetails(String componenet, String type, String condition, String parameter, String value) {
        System.out.println("The atatck details are as given below:");
        System.out.println("componenet: " + componenet);
        System.out.println("type: " + type);
        System.out.println("condition: " + condition);
        System.out.println("parameter: " + parameter);
        System.out.println("value: " + value);
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
        SimpleDateFormat formatter = new SimpleDateFormat("dd/MM/yyyy HH:mm:ss");
        Date date = new Date();
        Element el = doc.createElement("attack");
        el.appendChild(createAttackDetails(doc, "component_name", componentName));
        el.appendChild(createAttackDetails(doc, "type", attackType));
        System.out.println("FAILED CONDITION: " + cond);
        el.appendChild(createAttackDetails(doc, "failed_condition", cond));
        el.appendChild(createAttackDetails(doc, "variable_name", var));
        el.appendChild(createAttackDetails(doc, "corrupted_data", data));
        el.appendChild(createAttackDetails(doc, "time", formatter.format(date)));
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
