var d = document

function gid(id) {
	eval(`${id} = d.getElementById("${id}")`)
}

gid("formula")
gid("deduction")


