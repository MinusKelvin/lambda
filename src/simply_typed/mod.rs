use std::collections::HashMap;

pub struct Interpreter {
    globals: HashMap<String, Term>,
    names: HashMap<Term, Vec<String>>,
    types: HashMap<String, Type>,
    typenames: HashMap<Type, Vec<String>>,
    show_intermediate: bool,
    suppress: bool
}

#[derive(Clone, Debug, Eq)]
enum Term {
    Bound(usize),
    Application(Box<Term>, Box<Term>),
    Abstraction(String, Type, Box<Term>)
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Application(l1, r1), Term::Application(l2, r2)) =>
                l1 == l2 && r1 == r2,
            (Term::Abstraction(_, t1, e1), Term::Abstraction(_, t2, e2)) => e1 == e2 && t1 == t2,
            _ => false
        }
    }
}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        match self {
            Term::Bound(i) => {
                hasher.write_u8(0);
                i.hash(hasher);
            }
            Term::Abstraction(_, t, e) => {
                hasher.write_u8(1);
                t.hash(hasher);
                e.hash(hasher);
            }
            Term::Application(l, r) => {
                hasher.write_u8(2);
                l.hash(hasher);
                r.hash(hasher);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Type {
    Named(String),
    Function(Box<Type>, Box<Type>)
}

impl Type {
    fn display(
        &self, f: &mut std::fmt::Formatter, names: &HashMap<Type, Vec<String>>
    ) -> std::fmt::Result {
        if let Some(aliases) = names.get(self) {
            write!(f, "{}", aliases[0])
        } else {
            match self {
                Type::Named(name) => write!(f, "{}", name),
                Type::Function(from, to) => {
                    if names.contains_key(from) {
                        from.display(f, names)?;
                    } else {
                        if let Type::Function(_, _) = **from {
                            write!(f, "(")?;
                            from.display(f, names)?;
                            write!(f, ")")?;
                        } else {
                            from.display(f, names)?;
                        }
                    }
                    write!(f, " → ")?;
                    to.display(f, names)
                }
            }
        }
    }
}

impl Term {
    fn display(
        &self,
        f: &mut std::fmt::Formatter,
        name_bindings: &mut Vec<String>,
        typenames: &HashMap<Type, Vec<String>>
    ) -> std::fmt::Result {
        match self {
            Term::Bound(index) => {
                write!(f, "{}", name_bindings[name_bindings.len() - index])
            },
            Term::Application(left, right) => {
                if let Term::Abstraction(_, _, _) = **left {
                    write!(f, "(")?;
                    left.display(f, name_bindings, typenames)?;
                    write!(f, ")")?;
                } else {
                    left.display(f, name_bindings, typenames)?;
                }
                write!(f, " ")?;
                if let Term::Application(_, _) = **right {
                    write!(f, "(")?;
                    right.display(f, name_bindings, typenames)?;
                    write!(f, ")")
                } else {
                    right.display(f, name_bindings, typenames)
                }
            }
            Term::Abstraction(original_name, ty, term) => {
                let mut name = original_name.clone();
                while name_bindings.contains(&name) {
                    name += "'";
                }
                write!(f, "λ{}:", name)?;
                ty.display(f, typenames)?;
                write!(f, ". ")?;
                name_bindings.push(name);
                term.display(f, name_bindings, typenames)?;
                name_bindings.pop();
                Ok(())
            }
        }
    }

    fn check_type(&self, bindings: &mut Vec<Type>) -> Option<Type> {
        match self {
            Term::Bound(index) =>
                Some(bindings[bindings.len() - index].clone()),
            Term::Application(left, right) => {
                let left = left.check_type(bindings)?;
                let right = right.check_type(bindings)?;
                if let Type::Function(from, to) = left {
                    if *from == right {
                        Some(*to)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Term::Abstraction(_, in_ty, result) => {
                bindings.push(in_ty.clone());
                let result = result.check_type(bindings)?;
                bindings.pop();
                Some(Type::Function(Box::new(in_ty.clone()), Box::new(result)))
            }
        }
    }

    fn reduce(self) -> Result<Term, Term> {
        match self {
            Term::Bound(_) => Err(self),
            Term::Application(left, right) => match *left {
                Term::Abstraction(_, _, e) => Ok(e.substitute(*right, 1, 0)),
                e => match e.reduce() {
                    Ok(new) => Ok(Term::Application(Box::new(new), right)),
                    Err(old) => match right.reduce() {
                        Ok(new) => Ok(Term::Application(Box::new(old), Box::new(new))),
                        Err(oldr) => Err(Term::Application(Box::new(old), Box::new(oldr)))
                    }
                }
            },
            Term::Abstraction(name, t, e) => match e.reduce() {
                Ok(new) => Ok(Term::Abstraction(name, t, Box::new(new))),
                Err(old) => Err(Term::Abstraction(name, t, Box::new(old)))
            }
        }
    }

    fn substitute(self, with: Term, index: usize, inc: usize) -> Term {
        match self {
            Term::Bound(i) => if i > index {
                Term::Bound(i-1)
            } else if i == index {
                with.increment(inc, 0)
            } else {
                Term::Bound(i)
            }
            Term::Application(l, r) => Term::Application(
                Box::new(l.substitute(with.clone(), index, inc)),
                Box::new(r.substitute(with, index, inc))
            ),
            Term::Abstraction(s, t, e) => Term::Abstraction(
                s, t, Box::new(e.substitute(with, index + 1, inc + 1))
            )
        }
    }

    fn increment(self, by: usize, binders: usize) -> Term {
        match self {
            Term::Bound(i) => if i <= binders {
                Term::Bound(i)
            } else {
                Term::Bound(i + by)
            }
            Term::Application(l, r) => Term::Application(
                Box::new(l.increment(by, binders)),
                Box::new(r.increment(by, binders))
            ),
            Term::Abstraction(s, t, e) => Term::Abstraction(
                s, t, Box::new(e.increment(by, binders + 1))
            )
        }
    }
}

struct DisplayTerm<'a>(&'a Term, &'a HashMap<Type, Vec<String>>);
impl std::fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.display(f, &mut vec![], self.1)
    }
}

struct DisplayType<'a>(&'a Type, &'a HashMap<Type, Vec<String>>);
impl std::fmt::Display for DisplayType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.display(f, self.1)
    }
}

impl Interpreter {
    fn compute(&self, mut term: Term) -> Option<(Term, Type)> {
        if self.show_intermediate && !self.suppress {
            println!("  < {}", DisplayTerm(&term, &self.typenames));
        }
        let ty = term.check_type(&mut vec![])?;
        loop {
            match term.reduce() {
                Ok(new_term) => {
                    term = new_term;
                    if self.show_intermediate && !self.suppress {
                        println!(" β| {}", DisplayTerm(&term, &self.typenames));
                    }
                }
                Err(final_term) => {
                    return Some((final_term, ty))
                }
            }
        }
    }

    fn def(&mut self, name: String, term: Term) {
        use std::collections::hash_map::Entry;
        match self.globals.entry(name) {
            Entry::Occupied(mut entry) => {
                self.names.entry(term.clone())
                    .or_default()
                    .push(entry.key().clone());
                let old = entry.insert(term);
                let name = entry.key();
                if self.names[&old].len() == 1 {
                    self.names.remove(&old);
                } else {
                    let mut remove_index = 0;
                    let l = self.names.get_mut(&old).unwrap();
                    for (i, v) in l.iter().enumerate() {
                        if v == name {
                            remove_index = i
                        }
                    }
                    l.remove(remove_index);
                }
            }
            Entry::Vacant(entry) => {
                self.names.entry(term.clone())
                    .or_default()
                    .push(entry.key().clone());
                entry.insert(term);
            }
        }
    }

    fn typedef(&mut self, name: String, ty: Type) {
        use std::collections::hash_map::Entry;
        match self.types.entry(name) {
            Entry::Occupied(mut entry) => {
                self.typenames.entry(ty.clone())
                    .or_default()
                    .push(entry.key().clone());
                let old = entry.insert(ty);
                let name = entry.key();
                if self.typenames[&old].len() == 1 {
                    self.typenames.remove(&old);
                } else {
                    let mut remove_index = 0;
                    let l = self.typenames.get_mut(&old).unwrap();
                    for (i, v) in l.iter().enumerate() {
                        if v == name {
                            remove_index = i
                        }
                    }
                    l.remove(remove_index);
                }
            }
            Entry::Vacant(entry) => {
                self.typenames.entry(ty.clone())
                    .or_default()
                    .push(entry.key().clone());
                entry.insert(ty);
            }
        }
    }

    fn print_aliases(&self, term: &Term) {
        if let Some(aliases) = self.names.get(term) {
            print!("  |");
            for alias in aliases {
                print!(" = {}", alias);
            }
            println!();
        }
    }

    fn print_type_aliases(&self, ty: &Type) {
        if let Some(aliases) = self.typenames.get(ty) {
            print!("  |");
            for alias in aliases {
                print!(" = {}", alias);
            }
            println!();
        }
    }

    fn run<R: std::io::Read>(&mut self, from: R) {
        use std::io::{ BufRead, BufReader };
        use crate::Interpreter;
        let mut input = String::new();
        let show_intermediate = self.show_intermediate;
        let suppress = self.suppress;
        for line in BufReader::new(from).lines() {
            if let Ok(line) = line {
                input += &line;
                if self.evaluate(&input) {
                    input.clear()
                }
            }
        }
        self.show_intermediate = show_intermediate;
        self.suppress = suppress;
    }
}

impl crate::Interpreter for Interpreter {
    fn prompt(&self) -> &str {
        "λ→"
    }

    fn prompt_len(&self) -> usize {
        2
    }

    fn evaluate(&mut self, command: &str) -> bool {
        if command.starts_with("?") {
            let words: Vec<_> = command[1..].split_whitespace().collect();
            match words[0] {
                "about" => {
                    println!("{}", if words.len() == 1 {
                        include_str!("about.txt")
                    } else {
                        match words[1] {
                            page => {
                                println!("Unknown page: {}", page);
                                return true
                            }
                        }
                    });
                    true
                }
                "defs" => if words.len() > 1 {
                    match words[1] {
                        "numerals" => self.run(include_bytes!("defs/numerals.txt") as &[u8]),
                        e => println!("Unknown definition set: {}", e)
                    }
                    true
                } else {
                    println!("{}", include_str!("defs.txt"));
                    true
                }
                "suppress" => {
                    self.suppress = true;
                    true
                }
                "unsuppress" => {
                    self.suppress = false;
                    true
                }
                "show_intermediate" => {
                    self.show_intermediate = true;
                    true
                }
                "hide_intermediate" => {
                    self.show_intermediate = false;
                    true
                }
                "print" => {
                    for w in &words[1..] {
                        print!("{} ", w)
                    }
                    println!();
                    true
                }
                c => {
                    println!("Unknown command: {}", c);
                    true
                }
            }
        } else {
            match parse(&mut command.chars().peekable(), &self.globals, &self.types) {
                Ok(Command::Term(term)) => {
                    let result = self.compute(term);
                    if !self.suppress {
                        if let Some((result, ty)) = result {
                            println!("  > {}", DisplayTerm(&result, &self.typenames));
                            println!("  : {}", DisplayType(&ty, &self.typenames));
                            self.print_aliases(&result);
                        } else {
                            println!("  > The input is improperly typed.");
                        }
                    }
                    true
                }
                Ok(Command::Define(name, term)) => {
                    let result = self.compute(term);
                    if let Some((result, ty)) = result {
                        if !self.suppress {
                            println!("  > {} = {}", name, DisplayTerm(&result, &self.typenames));
                            println!("  : {}", DisplayType(&ty, &self.typenames));
                            self.print_aliases(&result);
                        }
                        self.def(name, result);
                    } else if !self.suppress {
                        println!("  > The input is improperly typed.");
                    }
                    true
                }
                Ok(Command::TypeDef(name, ty)) => {
                    if !self.suppress {
                        println!("  > {} = {}", name, DisplayType(&ty, &self.typenames));
                        self.print_type_aliases(&ty);
                    }
                    self.typedef(name, ty);
                    true
                }
                Ok(Command::Nothing) => true,
                Err(ParseError::Unfinished) => false,
                Err(ParseError::Failure(reason)) => {
                    println!("Parse error: {}", reason);
                    true
                }
            }
        }
    }
}

enum Command {
    Nothing,
    Term(Term),
    Define(String, Term),
    TypeDef(String, Type)
}

type Lexer<'a> = std::iter::Peekable<std::str::Chars<'a>>;

fn parse(
    chars: &mut Lexer, globals: &HashMap<String, Term>, types: &HashMap<String, Type>
) -> Result<Command, ParseError> {
    skip_whitespace(chars);
    if let Some(&c) = chars.peek() {
        if c.is_ascii_alphanumeric() || c == '_' {
            let ident = parse_ident(chars);
            match &*ident {
                "define" => parse_def(chars, globals, types).map(|(n, t)| Command::Define(n, t)),
                "typedef" => parse_typedef(chars, types).map(|(n, t)| Command::TypeDef(n, t)),
                _ => {
                    let term = parse_application(
                        resolve(&ident, globals)?,
                        chars, &mut vec![], globals, types
                    )?;
                    check_end(chars)?;
                    Ok(Command::Term(term))
                }
            }
        } else {
            let term = parse_term(chars, &mut vec![], globals, types)?;
            check_end(chars)?;
            Ok(Command::Term(term))
        }
    } else {
        Ok(Command::Nothing)
    }
}

fn parse_def(
    chars: &mut Lexer, globals: &HashMap<String, Term>, types: &HashMap<String, Type>
) -> Result<(String, Term), ParseError> {
    skip_whitespace(chars);
    let name = parse_ident(chars);
    skip_whitespace(chars);
    match chars.next() {
        Some('=') => {
            let term = parse_term(chars, &mut vec![], globals, types)?;
            check_end(chars)?;
            Ok((name, term))
        }
        Some(c) => Err(ParseError::Failure(format!("Expected =, got {}", c))),
        None => Err(ParseError::Unfinished)
    }
}

fn parse_typedef(
    chars: &mut Lexer, types: &HashMap<String, Type>
) -> Result<(String, Type), ParseError> {
    skip_whitespace(chars);
    let name = parse_ident(chars);
    skip_whitespace(chars);
    match chars.next() {
        Some('=') => {
            let ty = parse_type(chars, types)?;
            check_end(chars)?;
            Ok((name, ty))
        }
        Some(c) => Err(ParseError::Failure(format!("Expected =, got {}", c))),
        None => Err(ParseError::Unfinished)
    }
}

fn skip_whitespace(chars: &mut Lexer) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break
        }
    }
}

fn check_end(chars: &mut Lexer) -> Result<(), ParseError> {
    skip_whitespace(chars);
    if let Some(c) = chars.next() {
        Err(ParseError::Failure(format!("Unexpected {}", c)))
    } else {
        Ok(())
    }
}

fn parse_ident(chars: &mut Lexer) -> String {
    let mut s = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_ascii_alphanumeric() || c == '_' {
            s.push(c);
            chars.next();
        } else {
            break
        }
    }
    return s
}

fn parse_type(chars: &mut Lexer, types: &HashMap<String, Type>) -> Result<Type, ParseError> {
    skip_whitespace(chars);
    parse_function(match chars.peek() {
        Some(&'(') => parse_type_parens(chars, types),
        Some(&c) if c.is_ascii_alphanumeric() || c == '_' => {
            let name = parse_ident(chars);
            if let Some(ty) = types.get(&name) {
                Ok(ty.clone())
            } else {
                Ok(Type::Named(name))
            }
        }
        _ => Err(ParseError::Unfinished)
    }?, chars, types)
}

fn parse_type_parens(chars: &mut Lexer, types: &HashMap<String, Type>) -> Result<Type, ParseError> {
    if let Some('(') = chars.next() {
        let ty = parse_type(chars, types)?;
        skip_whitespace(chars);
        match chars.next() {
            Some(')') => Ok(ty),
            Some(c) => Err(ParseError::Failure(format!("Expected ) or ->, got {}", c))),
            None => Err(ParseError::Unfinished)
        }
    } else {
        unreachable!();
    }
}

fn parse_function(
    from: Type, chars: &mut Lexer, types: &HashMap<String, Type>
) -> Result<Type, ParseError> {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'-') => {
            chars.next();
            match chars.next() {
                Some('>') => {},
                Some(_) => return Err(ParseError::Failure("Incomplete -> token".to_string())),
                None => return Err(ParseError::Unfinished)
            }
            let to = parse_type(chars, types)?;
            parse_function(Type::Function(Box::new(from), Box::new(to)), chars, types)
        }
        Some(&'→') => {
            chars.next();
            let to = parse_type(chars, types)?;
            parse_function(Type::Function(Box::new(from), Box::new(to)), chars, types)
        }
        _ => Ok(from)
    }
}

fn parse_application(
    func: Term,
    chars: &mut Lexer,
    binders: &mut Vec<String>,
    globals: &HashMap<String, Term>,
    types: &HashMap<String, Type>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'(') => parse_application(Term::Application(
            Box::new(func), Box::new(parse_parens(chars, binders, globals, types)?)
        ), chars, binders, globals, types),
        Some(&'\\') | Some(&'λ') => {
            chars.next();
            Ok(Term::Application(
                Box::new(func),
                Box::new(parse_abstraction(chars, binders, globals, types)?)
            ))
        }
        Some(&c) if c.is_ascii_alphanumeric() || c == '_' =>
            parse_application(Term::Application(
                Box::new(func),
                Box::new(parse_variable(chars, binders, globals)?)
            ), chars, binders, globals, types),
        _ => Ok(func)
    }
}

fn parse_abstraction(
    chars: &mut Lexer,
    binders: &mut Vec<String>,
    globals: &HashMap<String, Term>,
    types: &HashMap<String, Type>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    binders.push(parse_ident(chars));
    skip_whitespace(chars);
    let ty = match chars.next() {
        Some(':') => parse_type(chars, types),
        Some(c) => Err(ParseError::Failure(format!("Expected :, got {}", c))),
        None => Err(ParseError::Unfinished)
    }?;
    match chars.next() {
        Some('.') => {
            let term = parse_term(chars, binders, globals, types)?;
            Ok(Term::Abstraction(binders.pop().unwrap(), ty, Box::new(term)))
        }
        Some(c) => Err(ParseError::Failure(format!("Expected ., got {}", c))),
        None => Err(ParseError::Unfinished)
    }
}

fn parse_parens(
    chars: &mut Lexer,
    binders: &mut Vec<String>,
    globals: &HashMap<String, Term>,
    types: &HashMap<String, Type>
) -> Result<Term, ParseError> {
    if let Some('(') = chars.next() {
        let term = parse_term(chars, binders, globals, types)?;
        skip_whitespace(chars);
        match chars.next() {
            Some(')') => Ok(term),
            Some(c) => Err(ParseError::Failure(format!("Expected ) or a lambda term, got {}", c))),
            None => Err(ParseError::Unfinished)
        }
    } else {
        unreachable!();
    }
}

fn parse_term(
    chars: &mut Lexer,
    binders: &mut Vec<String>,
    globals: &HashMap<String, Term>,
    types: &HashMap<String, Type>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'(') => parse_application(
            parse_parens(chars, binders, globals, types)?,
            chars, binders, globals, types
        ),
        Some(&'\\') | Some(&'λ') => {
            chars.next();
            parse_abstraction(chars, binders, globals, types)
        }
        Some(&c) if c.is_ascii_alphanumeric() || c == '_' =>
            parse_application(
                parse_variable(chars, binders, globals)?,
                chars, binders, globals, types
            ),
        Some(&c) => Err(ParseError::Failure(format!("Expected a lambda term, got {}", c))),
        None => Err(ParseError::Unfinished)
    }
}

fn parse_variable(
    chars: &mut Lexer, binders: &mut Vec<String>, globals: &HashMap<String, Term>
) -> Result<Term, ParseError> {
    let name = parse_ident(chars);
    for (i, binding) in binders.iter().rev().enumerate() {
        if *binding == name {
            return Ok(Term::Bound(i + 1))
        }
    }
    resolve(&name, globals)
}

fn resolve(name: &str, globals: &HashMap<String, Term>) -> Result<Term, ParseError> {
    globals.get(name).cloned().ok_or_else(
        || ParseError::Failure(format!(
            "This interpreter requires inputs to be closed, but {} is free in the input.",
            name
        ))
    )
}

enum ParseError {
    Unfinished,
    Failure(String)
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter {
            globals: HashMap::new(),
            names: HashMap::new(),
            typenames: HashMap::new(),
            types: HashMap::new(),
            show_intermediate: true,
            suppress: false
        }
    }
}