
// tokenize a full expression.
// Ex:
//  (Diff[a+Diff[(b+c)]]+g)=(x+b+0.5)
//
// tokens:
// (
// )
// [
// ]
// [a-zA-z][a-zA-z0-9]*
// [0-9](.?[0-9])*
// ignore whitespace as implicit delimiter
//
// Include spaces to disambiguate negative sign from subtraction
// Include parenthesis on all operators, because there is no precedence
function tokenize(s) {
    s = "(" + s + ")";
    var isWsp = function(c) {
        return c === ' ' || c === '\n' || c === '\r' || c === '\t';
    }
    var isAlpha = function(c) {
        return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
    }
    var isNum = function(c) {
        return '0' <= c && c <= '9';
    }
    var isAlphaNum = function(c) {
        return isAlpha(c) || isNum(c);
    }
    var isBracket = function(c) {
        return '(' === c || ')' === c || '[' === c || ']' === c || '{' === c || '}' === c;
    }
    var isUnknown = function(c) {
        return !(isWsp(c) || isAlphaNum(c) || isBracket(c));
    }
    var isFloat = function(c) {
        return isAlphaNum(c) || (c == '.');
    }
    
    var i = -1;
    var nextChar = function() {
      i++;
      return s[i];
    }
    var lookAhead = function() {
        return s[i+1];
    }
    var moreChars = function() {
        return (i+1) < s.length;
    }
    var undoChar = function() {
        i--;
    }

    var LOOKFORTOKEN=0;
    var CONSUMINGTOKEN=1;
    var CONSUMINGOPERATOR=2;
    var CONSUMINGNUMBER=3;

    var state = LOOKFORTOKEN;

    var t = "";
    var appendToken = function(c, s) {
        t = t + c;
        state = s;
    }
    var clearToken = function() {
        t = "";
        state = LOOKFORTOKEN;
    }
    var tokens = [];

    var acceptToken = function(c) {
        tokens.push(c);
        clearToken();
    }

    while(moreChars()) {
        var c = nextChar();
        if(state === LOOKFORTOKEN) {
            clearToken();
            if(isWsp(c)) {
                continue;
            }
            if(isAlpha(c)) {
                appendToken(c, CONSUMINGTOKEN);
                continue;
            }
            if(isBracket(c)) {
                tokens.push(c);
                continue;
            }
            // negative number special case
            if(c === '-' && isNum(lookAhead(c))) {
                c = nextChar();
                t = "-";
                appendToken(c, CONSUMINGNUMBER);
                continue;
            }
            
            if(isNum(c)) {
                appendToken(c, CONSUMINGNUMBER);
                continue;
            }
            // Assume that everything else is a compound operator, like ++, =>, etc.
            appendToken(c, CONSUMINGOPERATOR);
            continue;
        }
        if(state === CONSUMINGTOKEN && isAlphaNum(c)) {
            appendToken(c, state);
            continue;
        }
        if(state === CONSUMINGOPERATOR && isUnknown(c)) {
            appendToken(c, state);
            continue;
        }
        if(state === CONSUMINGNUMBER && isFloat(c)) {
            appendToken(c, state);
            continue;
        }
        acceptToken(t);
        undoChar();
        continue;
    }
    return tokens;
}

// {"op":"+",[a,b,c]}
// {"fn":"Diff",[a,b,c]}
function parse(t) {
    // stack
    var s = []
    var evaluateItem = function() {
        if(item === "]") {
            var s2 = [];
            var top = s.pop();
            while(true) {
                top = s.pop();
                if(top === "[") {
                    break;
                }
                s2.push(top);
                if(s.length == 0) {
                    break;
                }
            }
            // functions are prefix
            var fn = s.pop();
            var result = {
                fn: fn,
                a: []
            };
            if(s2.length > 0) {
                result.op = s2[1];
            }
            s2.reverse();
            for(var i=0; i<s2.length; i = i + 2) {
                result.a.push(s2[i]);
            }
            s.push(result);
        }
        if(item === ")") {
            var s2 = [];
            var top = s.pop();
            while(true) {
                top = s.pop();
                if(top === "(") {
                    break;
                }
                s2.push(top);
                if(s.length == 0) {
                    break;
                }
            }
            // parenthesis are infix ops.  make an op object for it
            if(s2.length == 1) {
                s.push(s2[0]);
            } else {
                // Assume that everything associates and is same operator, as we have no op precedences yet
                var result = {
                    op: s2[1],
                    a: [],
                };
                s2.reverse();
                for(var i=0; i<s2.length; i = i + 2) {
                    result.a.push(s2[i]);
                }
                s.push(result);
            }
        }
    }
    for(var i=0; i<t.length; i++) {
        // Push items into the stack in original order
        var item = t[i];
        s.push(item);
        evaluateItem();
    }
    console.log(JSON.stringify(s[s.length-1]));
}

var rules = [
    {rule:"(a=b) = (b=a)",name:"eq commute"},
    {rule:"(a=b) = a",name:"eq lchoose"},
    {rule:"(a=b) = b",name:"eq rchoose"},
    {rule:"(a+b) = (b+a)",name:"commute +"},
    {rule:"(c * (a+b)) = ((c*a) + (c*b))",name:"ldist * over +"},
    {rule:"((a+b) * c) = ((a*c) + (b*c))",name:"rdist * over +"},
    {rule:"a/b",name:"div intro",require:"b != 0"},
    {rule:"(a/b) = (1/(b/a))",name:"inv /"},
    {rule:"(a+0) = a",name:"identity +"},
    {rule:"(a*1) = a",name:"identity *"},
    {rule:"(a^1) = a",name:"identity ^"},
    {rule:"(a^0) = 1",name:"null ^"},
    {rule:"(a * (a ^ b)) = (a ^ (b+1))",name:"exp *"},
    {rule:"D[a+c] = D[a]",name:"diff constant",require:"D[c] = 0"}
];

function findMatches(s,ruleSet) {
    var p = parse(tokenize(s));
    for(var i=0; i<ruleSet.length; i++) {
        var r = ruleSet[i];
        var m = parse(tokenize(r));
        if(m.op === "=") {
            var ml = m.a[0];
            var mr = m.a[1];
            // match rules to expr -- parens are associative operator:
            //     (a+b) match (x+y+z)
            //        (x)+(y+z)
            //        (x+y)+(z)
            // focus on an op... what matches?
            var mismatched = false;
            if(ml.op && ml.a && p.op && p.a) {
                
                for(var j=0; j<ml.a.length; j++) {

                }    
            }
        } else {

        }
    }
}

for(var i=0; i<rules.length; i++) {
    parse(tokenize(rules[i].rule));
}
