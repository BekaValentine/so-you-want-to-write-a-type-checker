/*
 *  Making representations of types
 */
 
var Foo = { tag: "Foo" };
var Bar = { tag: "Bar" };
var Baz = { tag: "Baz" };

function prod(a,b) {
    return { tag: "*", left: a, right: b };
}

function arr(a,b) {
    return { tag: "->", arg: a, ret: b };
}


/*
 *  A type
 *  ======
 */
function judgment_type(a) {
    
    /*  -------- Foo Formation
     *  Foo type
     *
     *  -------- Bar Formation
     *  Bar type
     *
     *  -------- Baz Formation
     *  Baz type
     */
    if ("Foo" == a.tag || "Bar" == a.tag || "Baz" == a.tag) {
        
        return true;
        
    }
    
    /*  A type    B type
     *  ---------------- * Formation
     *      A*B type
     */
    else if ("*" == a.tag) {
        
        return judgment_type(a.left) && judgment_type(a.right);
        
    }
    
    /*  A type    B type
     *  ---------------- -> Formation
     *    A -> B type
     */
    else if ("->" == a.tag) {
        
        return judgment_type(a.arg) && judgment_type(a.ret);
        
    }
    
    /*
     *  Nothing else is a type
     */ 
    else {
        
        return false;
        
    }
}



/*
 *  Making representations of contexts
 */
 
var empty = { tag: "<>" }

function snoc(g,x,a) {
    return { tag: ",:", rest: g, name: x, type: a };
}

/*
 *  Testing whether or not a variable is in a context
 */
function not_in(n, g) {
    if ("<>" == g.tag) {
        
        return true;
        
    } else {
        
        if (n == g.name) {
            
            return false;
            
        } else {
            
            return not_in(n, g.rest);
            
        }
        
    }
}


/*
 * G ctx
 * =====
 */
function judgment_ctx(g) {
    
    /*
     *  ------ empty context
     *  <> ctx
     */
    if ("<>" == g.tag) {
        
        return true;
        
    }
    
    /*
     *  G ctx    A type    x is not in G
     *  -------------------------------- new var
     *           G, x : A ctx
     */
    else if (",:" == g.tag) {
        
        return judgment_ctx(g.rest) &&
               judgment_type(g.type) &&
               not_in(g.name, g.rest);
        
    }
    
    /*
     *  Nothing else is a context
     */
    else {
        
        return false;
        
    }
}




/*
 *  Making representations of terms
 */

function pair(m,n) {
  return { tag: "(,)", first: m, second: n };
}

function split(p, x, a, y, b, m) {
    return { tag: "split",
             pair: p,
             name_x: x, type_a: a,
             name_y: y, type_b: b,
             body: m };
}

function lam(x,m) {
    return { tag: "lam", name: x, body: m };
}

function app(m,n,a) {
    return { tag: "app", fun: m, arg: n, type_arg: a };
}

function v(n) {
    return { tag: "variable", name: n };
}

/*
 *  Checking if two types are equal
 */
function type_equality(a,b) {
    
    if (("Foo" == a.tag && "Foo" == b.tag) ||
        ("Bar" == a.tag && "Bar" == b.tag) ||
        ("Baz" == a.tag && "Baz" == b.tag)) {
        
        return true;
        
    } else if ("*" == a.tag && "*" == b.tag) {
        
        return type_equality(a.left, b.left) && type_equality(a.right, b.right);
        
    } else if ("->" == a.tag && "->" == b.tag) {
        
        return type_equality(a.arg, b.arg) && type_equality(a.ret, b.ret);
        
    } else {
        
        return false;
        
    }
    
}

/*
 *  Checking if a variable has a type in a context
 */
function var_has_type(n,a,g) {
    if ("<>" == g.tag) {
        
        return false;
        
    } else if (",:" == g.tag) {
        
        if (n == g.name) {
            
            return type_equality(a, g.type);
            
        } else {
            
            return var_has_type(n, a, g.rest);
            
        }
        
    }
}




/*
 *  G !- M : A
 *  ==========
 */
function judgment_check(g, m, a) {
    
    /*
     *  G !- M : A    G !- N : B
     *  ------------------------ * Intro
     *      G !- (M,N) : A*B
     */
    if ("(,)" == m.tag && "*" == a.tag) {
        
        return judgment_check(g, m.first, a.left) &&
               judgment_check(g, m.second, a.right);
        
    }
    
    /*
     *  G !- P : A*B    G, x : A, y : B !- M : C
     *  ----------------------------------------- * Elim
     *  G !- split P as (x :: A, y :: B) in M : C
     */
    else if ("split" == m.tag) {
        
        return judgment_check(g, m.pair, prod(m.type_a, m.type_b)) &&
               judgment_check(snoc(snoc(g, m.name_x, m.type_a), m.name_y, m.type_b), m.body, a);
    
    }
    
    /*
     *  G, x : A !- M : B
     *  ------------------ -> Intro
     *  G !- \x.M : A -> B
     */
    else if ("lam" == m.tag && "->" == a.tag) {
        
        return judgment_check(snoc(g, m.name, a.arg), m.body, a.ret);
        
    }
    
    /*
     *  G !- M : A -> B    G !- N : A
     *  ----------------------------- -> Elim
     *     G !- app(M,N :: A) : B
     */
    else if ("app" == m.tag) {
        
        return judgment_check(g, m.fun, arr(m.type_arg, a)) &&
               judgment_check(g, m.arg, m.type_arg);
        
    }
    
    /*
     *  x has type A in G
     *  ----------------- variable
     *     G !- x : A
     */
    else if ("variable" == m.tag) {
        
        return var_has_type(m.name, a, g);
        
    }
    
    /*
     *  Nothing else is well-typed
     */
    else {
        
        return false;
        
    }
    
}
