$(document).ready(function()
{
	libtitle = $("h1.libtitle")[0].innerHTML
	title = libtitle.slice(libtitle.indexOf(" ") + 1).replace(" [TODO]", "") + " | Typonomikon"
	$("title")[0].innerHTML	= title
	
	console.log(title)
	
	$("body")[0].id = "main"

	$(".code").each(function()
	{
		$(this).addClass("code-tight")
	})

	$("#footer").remove()
})
