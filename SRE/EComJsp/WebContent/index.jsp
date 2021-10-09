<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>Insert title here</title>
</head>
<body>
  <form method="get" action="login.jsp">
  <h2>Login</h2> 
  <table>
    <tr>
      <td>Enter your username:</td>
      <td><input type='text' name='username' /></td>
    </tr>
    <tr>
      <td>Enter your password:</td>
      <td><input type='text' name='password' /></td>
    </tr>
  </table>
  <br />
  <input type="submit" value='LOGIN' />
  <input type="reset" value='CLEAR' />
  </form>
</body>
</html>