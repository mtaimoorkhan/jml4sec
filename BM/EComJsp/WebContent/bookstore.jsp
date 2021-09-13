<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>Book Store</title>
</head>
<body>
<h1>My Book Store</h1>
<form method='get' action='query.jsp'>
Choose an Author: <select name='author' size='1'>
<option value=''>Select...</option>
<option value='Tan Ah Teck'>Tan Ah Teck</option>
<option value='Mohammad Ali'>Mohammad Ali</option>
<option value='Kumar'>Kumar</option>
<option value='Kevin Jones'>Kevin Jones</option>
</select><br />
<p>OR</p>
Search Title or Author: <input type='text' name='author_name' />
<br /><br />

<p>OR</p>
Search by Book ID: <input type='text' name='book_id' />
<br /><br />


<input type='submit' value='SEARCH' />
<input type='reset' value='CLEAR' />
</form>
</body>
</html>