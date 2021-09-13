package utility.com.greenwich;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.StringReader;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.stream.StreamSource;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class greMarshaller {

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
            // File file = new File("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/student.xml");
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
}
