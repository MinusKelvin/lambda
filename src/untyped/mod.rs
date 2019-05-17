use std::collections::HashMap;

pub struct Interpreter {
    globals: HashMap<String, Term>,
    names: HashMap<Term, Vec<String>>,
    show_intermediate: bool,
    suppress: bool
}

#[derive(Clone, Debug, Eq)]
enum Term {
    Bound(usize),
    Application(Box<Term>, Box<Term>),
    Abstraction(String, Box<Term>)
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Application(l1, r1), Term::Application(l2, r2)) =>
                l1 == l2 && r1 == r2,
            (Term::Abstraction(_, e1), Term::Abstraction(_, e2)) => e1 == e2,
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
            Term::Abstraction(_, e) => {
                hasher.write_u8(1);
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

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.display(f, &mut vec![])
    }
}

impl Term {
    fn display(
        &self, f: &mut std::fmt::Formatter, name_bindings: &mut Vec<String>
    ) -> std::fmt::Result {
        match self {
            Term::Bound(index) => {
                write!(f, "{}", name_bindings[name_bindings.len() - index])
            },
            Term::Application(left, right) => {
                if let Term::Abstraction(_, _) = **left {
                    write!(f, "(")?;
                    left.display(f, name_bindings)?;
                    write!(f, ")")?;
                } else {
                    left.display(f, name_bindings)?;
                }
                write!(f, " ")?;
                if let Term::Application(_, _) = **right {
                    write!(f, "(")?;
                    right.display(f, name_bindings)?;
                    write!(f, ")")
                } else {
                    right.display(f, name_bindings)
                }
            }
            Term::Abstraction(original_name, term) => {
                let mut name = original_name.clone();
                while name_bindings.contains(&name) {
                    name += "'";
                }
                write!(f, "λ{}. ", name)?;
                name_bindings.push(name);
                term.display(f, name_bindings)?;
                name_bindings.pop();
                Ok(())
            }
        }
    }

    fn reduce(self) -> Result<Term, Term> {
        match self {
            Term::Bound(_) => Err(self),
            Term::Application(left, right) => match *left {
                Term::Abstraction(_, e) => Ok(e.substitute(*right, 1, 0)),
                e => match e.reduce() {
                    Ok(new) => Ok(Term::Application(Box::new(new), right)),
                    Err(old) => match right.reduce() {
                        Ok(new) => Ok(Term::Application(Box::new(old), Box::new(new))),
                        Err(oldr) => Err(Term::Application(Box::new(old), Box::new(oldr)))
                    }
                }
            },
            Term::Abstraction(name, e) => match e.reduce() {
                Ok(new) => Ok(Term::Abstraction(name, Box::new(new))),
                Err(old) => Err(Term::Abstraction(name, Box::new(old)))
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
            Term::Abstraction(s, e) => Term::Abstraction(
                s, Box::new(e.substitute(with, index + 1, inc + 1))
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
            Term::Abstraction(s, e) => Term::Abstraction(
                s, Box::new(e.increment(by, binders + 1))
            )
        }
    }
}

impl Interpreter {
    fn compute(&self, mut term: Term) -> Term {
        if self.show_intermediate && !self.suppress {
            println!(" < {}", &term);
        }
        loop {
            match term.reduce() {
                Ok(new_term) => {
                    term = new_term;
                    if self.show_intermediate && !self.suppress {
                        println!("β| {}", &term);
                    }
                }
                Err(final_term) => {
                    return final_term
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

    fn print_aliases(&self, term: &Term) {
        if let Some(aliases) = self.names.get(term) {
            print!(" |");
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
        let supress = self.suppress;
        for line in BufReader::new(from).lines() {
            if let Ok(line) = line {
                input += &line;
                if self.evaluate(&input) {
                    input.clear()
                }
            }
        }
        self.show_intermediate = show_intermediate;
        self.suppress = supress;
    }
}

impl crate::Interpreter for Interpreter {
    fn prompt(&self) -> &str { "λ" }
    fn prompt_len(&self) -> usize { 1 }

    fn evaluate(&mut self, command: &str) -> bool {
        if command.starts_with("?") {
            let words: Vec<_> = command[1..].split_whitespace().collect();
            match words[0] {
                "help" => {
                    println!("{}", include_str!("help.txt"));
                    true
                }
                "defs" => if words.len() > 1 {
                    match words[1] {
                        "standard" => self.run(include_bytes!("defs/standard.txt") as &[u8]),
                        "boolean" => self.run(include_bytes!("defs/boolean.txt") as &[u8]),
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
            match parse(&mut command.chars().peekable(), &self.globals) {
                Ok(Command::Term(term)) => {
                    let result = self.compute(term);
                    if !self.suppress {
                        println!(" > {}", result);
                        self.print_aliases(&result);
                    }
                    true
                }
                Ok(Command::Alias(name, term)) => {
                    if !self.suppress {
                        println!(" > {} = {}", name, term);
                        self.print_aliases(&term);
                    }
                    self.def(name, term);
                    true
                }
                Ok(Command::Define(name, term)) => {
                    let result = self.compute(term);
                    if !self.suppress {
                        println!(" > {} = {}", name, result);
                        self.print_aliases(&result);
                    }
                    self.def(name, result);
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
    Alias(String, Term),
    Define(String, Term)
}

type Lexer<'a> = std::iter::Peekable<std::str::Chars<'a>>;

fn parse(chars: &mut Lexer, globals: &HashMap<String, Term>) -> Result<Command, ParseError> {
    skip_whitespace(chars);
    if let Some(&c) = chars.peek() {
        if c.is_ascii_alphanumeric() || c == '_' {
            let ident = parse_ident(chars);
            match &*ident {
                "alias" => parse_def(chars, globals).map(|(n, t)| Command::Alias(n, t)),
                "define" => parse_def(chars, globals).map(|(n, t)| Command::Define(n, t)),
                _ => {
                    let term = parse_application(
                        resolve(&ident, globals)?,
                        chars, &mut vec![], globals
                    )?;
                    check_end(chars)?;
                    Ok(Command::Term(term))
                }
            }
        } else {
            let term = parse_term(chars, &mut vec![], globals)?;
            check_end(chars)?;
            Ok(Command::Term(term))
        }
    } else {
        Ok(Command::Nothing)
    }
}

fn parse_def(chars: &mut Lexer, globals: &HashMap<String, Term>) -> Result<(String, Term), ParseError> {
    skip_whitespace(chars);
    let name = parse_ident(chars);
    skip_whitespace(chars);
    match chars.next() {
        Some('=') => {
            let term = parse_term(chars, &mut vec![], globals)?;
            check_end(chars)?;
            Ok((name, term))
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

fn parse_application(
    func: Term, chars: &mut Lexer, binders: &mut Vec<String>, globals: &HashMap<String, Term>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'(') => parse_application(Term::Application(
            Box::new(func), Box::new(parse_parens(chars, binders, globals)?)
        ), chars, binders, globals),
        Some(&'\\') | Some(&'λ') => {
            chars.next();
            Ok(Term::Application(
                Box::new(func),
                Box::new(parse_abstraction(chars, binders, globals)?)
            ))
        }
        Some(&c) if c.is_ascii_alphanumeric() || c == '_' =>
            parse_application(Term::Application(
                Box::new(func),
                Box::new(parse_variable(chars, binders, globals)?)
            ), chars, binders, globals),
        _ => Ok(func)
    }
}

fn parse_abstraction(
    chars: &mut Lexer, binders: &mut Vec<String>, globals: &HashMap<String, Term>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    binders.push(parse_ident(chars));
    skip_whitespace(chars);
    match chars.next() {
        Some('.') => {
            let term = parse_term(chars, binders, globals)?;
            Ok(Term::Abstraction(binders.pop().unwrap(), Box::new(term)))
        }
        Some(c) => Err(ParseError::Failure(format!("Expected ., got {}", c))),
        None => Err(ParseError::Unfinished)
    }
}

fn parse_parens(
    chars: &mut Lexer, binders: &mut Vec<String>, globals: &HashMap<String, Term>
) -> Result<Term, ParseError> {
    if let Some('(') = chars.next() {
        let term = parse_term(chars, binders, globals)?;
        skip_whitespace(chars);
        match chars.next() {
            Some(')') => Ok(term),
            Some(c) => Err(ParseError::Failure(format!("Expected ), got {}", c))),
            None => Err(ParseError::Unfinished)
        }
    } else {
        unreachable!();
    }
}

fn parse_term(
    chars: &mut Lexer, binders: &mut Vec<String>, globals: &HashMap<String, Term>
) -> Result<Term, ParseError> {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'(') => parse_application(
            parse_parens(chars, binders, globals)?,
            chars, binders, globals
        ),
        Some(&'\\') | Some(&'λ') => {
            chars.next();
            parse_abstraction(chars, binders, globals)
        }
        Some(&c) if c.is_ascii_alphanumeric() || c == '_' =>
            parse_application(
                parse_variable(chars, binders, globals)?,
                chars, binders, globals
            ),
        Some(&c) => Err(ParseError::Failure(format!("Unexpected {}", c))),
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
        || ParseError::Failure(format!("No such variable: {}", name))
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
            show_intermediate: true,
            suppress: false
        }
    }
}