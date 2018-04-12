
function cmljs_append(a, b) {
  if (Array.isArray(a) && Array.isArray(b)) {
    return a[0].cmlg_char
      ? a.concat(b).reduce((a, b) => a + b.cmlg_char, "")
      : a.concat(b)
  } else if (typeof a === 'string' && typeof b === 'string') {
    return a + b
  } else if (Array.isArray(a) && typeof b === 'string') {
    return a.reduce((a, b) => a + b.cmlg_char, "") + b
  } else if (typeof a === 'string' && Array.isArray(b)) {
    return b.reduce((a, b) => a + b.cmlg_char, a)
  }
}

function every2(as, bs, f) {
  return Array.isArray(as)
    && Array.isArray(bs)
    && as.length === bs.length
    && as.every((a, i) => f(a, bs[i]))
}

function cmljs_eq(a, b) {
	return (a instanceof bigInt && b instanceof bigInt && a.equals(b))
    || (a.cmlg_char && a.cmlg_char === b.cmlg_char)
		|| (a.cmlg_v && b.cmlg_v && a === b)
		|| (a.cmlg_array && b.cmlg_array && a === b)
		|| (Array.isArray(a) && Array.isArray(b) && every2(a, b, cmljs_eq))
		|| (a.tuple && b.tuple && every2(a.cmlg_tuple, b.cmlg_tuple, cmljs_eq))
		|| (a.constructor === b.constructor && every2(a.cmlg_fields, b.cmlg_fields, cmljs_eq))
		|| (typeof a === 'function' && typeof b === 'function')
		|| a === b
}

function cmljs_doesmatch(pat, content) {
  return pat.pany === true
    || pat.pvar === true
    || typeof content !== 'undefined'
      && ((pat.plit && cmljs_eq(pat.plit, content))
        || (pat.pref && cmljs_doesmatch(pat.pref, content.cmlg_v))
        || (pat.array && Array.isArray(content)
          && (typeof pat.head === 'undefined' ? content.length === 0
            : cmljs_doesmatch(pat.head, content[0])
              && cmljs_doesmatch(pat.tail, content.slice(1))))
        || (pat.tuple && every2(pat.tuple, content.cmlg_tuple, cmljs_doesmatch))
        || (pat.cls && content instanceof pat.cls
          && every2(pat.fields, content.cmlg_fields, cmljs_doesmatch)))
    || false
}

module.exports = { cmljs_append, cmljs_eq, cmljs_doesmatch }

