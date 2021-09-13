<%@page import="db.com.greenwich.*,shopping.com.greenwich.*,javax.servlet.http.*, java.sql.*"%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>Order Details</title>
</head>
<body>
<h3>Thank you for booking with us</h3>
<%JBookShop.checkout(request, response,session); %>
</body>
</html>