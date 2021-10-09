package annotation.com.greenwich;

public @interface compromised_behavior {

    String requires() default "first";

    String assignable() default "first";

    String reads() default "first";

    String writes() default "first";

    String ensures() default "first";

    String alarms() default "first";

    String before() default "first";

    String after() default "first";
}
