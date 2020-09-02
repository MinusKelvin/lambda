mod untyped;
mod simply_typed;

use rustyline::Editor;
use rustyline::error::ReadlineError;

const HELP_TEXT: &str = include_str!("help.txt");

fn main() {
    println!("{}", HELP_TEXT);

    let mut rl = Editor::<()>::new();
    let mut interpreter: Box<dyn Interpreter> = Box::new(untyped::Interpreter::default());

    loop {
        let prompt = String::from(interpreter.prompt()) + ": ";
        match rl.readline(&prompt) {
            Ok(mut line) => {
                if line.starts_with("?") {
                    let words: Vec<_> = line[1..].split_whitespace().collect();
                    if words.len() == 0 {
                        println!("{}", HELP_TEXT);
                        continue
                    } else if words[0] == "exit" || words[0] == "quit" || words[0] == "q" {
                        break
                    } else if words[0] == "switch" {
                        if words.len() == 1 {
                            println!("{}", include_str!("variants.txt"))
                        } else {
                            match words[1] {
                                "untyped" =>
                                    interpreter = Box::new(untyped::Interpreter::default()),
                                "simply" =>
                                    interpreter = Box::new(simply_typed::Interpreter::default()),
                                v => println!("Unknown variant: {}", v)
                            }
                        }
                        continue
                    }
                }
                while !interpreter.evaluate(&line) {
                    let prompt = " ".repeat(interpreter.prompt_len()) + "| ";
                    match rl.readline(&prompt) {
                        Ok(newline) => {
                            line += &newline;
                        }
                        Err(_) => break
                    }
                }
            }
            Err(ReadlineError::Eof) | Err(ReadlineError::Interrupted) => break,
            Err(other) => println!("???: {}", other)
        }
    }
}

trait Interpreter {
    fn prompt(&self) -> &str;
    fn prompt_len(&self) -> usize;
    fn evaluate(&mut self, command: &str) -> bool;
}