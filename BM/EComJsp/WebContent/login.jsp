
<%@page import="db.com.greenwich.*, java.sql.*,shopping.com.greenwich.*,javax.servlet.http.*,java.io.*"%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>Insert title here</title>
</head>
<body>
<%
String userName = request.getParameter("username");
String password = request.getParameter("password");
 if (JBookShop.isLogin(userName,password,request,response)){
	 response.setStatus(response.SC_MOVED_TEMPORARILY);
	 JBookShop.redirectToPage(response, "Location", "bookstore.jsp");
	 //response.setHeader("Location", "bookstore.jsp");
 }
 else{
	 PrintWriter outt=response.getWriter();
	 outt.println("<h2>UnSucessful Login</h2>");
 }
%> 
</body>
</html>