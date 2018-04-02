
function every2(as, bs, f) {
  return Array.isArray(as)
    && Array.isArray(bs)
    && as.length === bs.length
    && as.every((a, i) => f(a, bs[i]))
}

function cmljs_eq(a, b) {
	return (a instanceof bigInt && b instanceof bigInt && a.equals(b))
    || (a.cmlg_char === b.cmlg_char)
		|| (a.pref && b.pref && cmljs_eq(a.cmlg_v, b.cmlg_v))
		|| (Array.isArray(a) && Array.isArray(b) && every2(a, b, cmljs_eq))
		|| (a.tuple && b.tuple && every2(a.cmlg_tuple, b.cmlg_tuple, cmljs_eq))
		|| (a.constructor === b.constructor && every2(a.cmlg_fields, b.cmlg_fields, cmljs_eq))
		|| (typeof a === 'function' && typeof b === 'function')
		|| a === b
}

function doesmatch(pat, content) {
  return pat.pany === true
    || pat.pvar === true
    || typeof content !== 'undefined'
      && ((pat.plit && cmljs_eq(pat.plit, content))
        || (pat.pref && doesmatch(pat.pref, content.cmlg_v))
        || (pat.array && Array.isArray(content)
          && (typeof pat.head === 'undefined' ? content.length === 0
            : doesmatch(pat.head, content[0])
              && doesmatch(pat.tail, content.slice(1))))
        || (pat.tuple && every2(pat.tuple, content.cmlg_tuple, doesmatch))
        || (pat.cls && content instanceof pat.cls
          && every2(pat.fields, content.cmlg_fields, doesmatch)))
    || false
}

module.exports = {
	cmljs_eq, doesmatch
}

