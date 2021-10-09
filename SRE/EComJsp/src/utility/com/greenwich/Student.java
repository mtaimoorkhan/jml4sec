package utility.com.greenwich;

import javax.xml.bind.annotation.*;
import utility.com.greenwich.Uty;

@XmlRootElement
public class Student {

    private String name;

    private int id;

    private String subject;

    Student() {
    }

    Student(String name, int id, String subject) {
        this.name = name;
        this.id = id;
        this.subject = subject;
    }

    @XmlElement
    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    @XmlElement
    public int getId() {
        return id;
    }

    /*@ compromised_behavior
	    alarms id < 10 ==> MarshallingError; 
	    */
    public void setId(int id) {
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        if (id < 10)
            Uty.addAttckDetails("setId", "MarshallingError", "id < 10", "id", id);
        assert (id < 10) : "MarshallingError";
        this.id = id;
        System.out.println(" callerd");
    }

    @XmlElement
    public String getSubject() {
        return subject;
    }

    public void setSubject(String subject) {
        this.subject = subject;
    }
}
