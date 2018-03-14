
const addGenPrefix = name => 'cmlg_' + name
const tupleProp = addGenPrefix('tuple')
const refProp = addGenPrefix('v')
const fieldsProp = addGenPrefix('fields')

function every2(as, bs, f) {
  return Array.isArray(as)
    && Array.isArray(bs)
    && as.length === bs.length
    && as.every((a, i) => f(a, bs[i]))
}

function cmljs_eq(a, b) {
	return a instanceof bigInt && b instanceof bigInt
		? a.equals(b)
		: (typeof a === 'function' && typeof b === 'function') || a === b
}

function doesmatch(pat, content) {
  return typeof content !== 'undefined' && (
    pat.pany === true
    || pat.pvar === true
    || (pat.plit && cmljs_eq(pat.plit, content))
    || (pat.pref && doesmatch(pat.pref, content[refProp]))
    || (pat.array && Array.isArray(content)
      && (typeof pat.head === 'undefined' ? content.length === 0
        : doesmatch(pat.head, content[0]) && doesmatch(pat.tail, content.slice(1))))
    || (pat.tuple && every2(pat.tuple, content[tupleProp], doesmatch)))
    || (pat.cls && content instanceof pat.cls && every2(pat.fields, content[fieldsProp], doesmatch))
    || false
}

module.exports = {
	cmljs_eq, doesmatch
}

