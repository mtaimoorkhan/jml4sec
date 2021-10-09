<%@page import="db.com.greenwich.*,shopping.com.greenwich.*,javax.servlet.http.*, java.sql.*"%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>My Cart</title>
</head>
<body>
<form method='get' action='checkout.jsp'>
<input type='hidden' name='id' value='1002' />
<% JBookShop.addToCart(request, response, request.getSession(true)); %>
<input type='submit' value='Checkout' />
<p>Please fill in your particular before checking out:</p>
<table>
<tr>
<td>Enter your Name:</td>
<td><input type='text' name='cust_name' /></td></tr>
<tr>
<td>Enter your Email:</td>
<td><input type='text' name='cust_email' /></td></tr>
<tr>
<td>Enter your Phone Number:</td>
<td><input type='text' name='cust_phone' /></td></tr>
</table>

</form>
</body>
</html>