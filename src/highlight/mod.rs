use std::io;

use nom::bytes::complete::{tag, take_till};
use nom::IResult;

use crate::custom_markdown::StrWrite;

pub mod java;

pub fn highlight<W: StrWrite>(mut w: W, s: &str) -> io::Result<()> {
    let xd: IResult<&str, &str, ()> = take_till(|c| c == '/')(s);
    let (after, before) = xd.unwrap();
    w.write_str(before)?;
    w.write_str("super")?;
    let xd: IResult<&str, &str, ()> = tag("//")(after);
    let (rest, tag) = xd.unwrap();
    w.write_str(tag)?;
    let xd: IResult<&str, &str, ()> = take_till(|c| c == '\n')(rest);
    let (last, comment) = xd.unwrap();
    w.write_str(comment)?;
    w.write_str("super")?;
    w.write_str(last)?;
    Ok(())
}

#[cfg(test)]
mod test {
    /*
    class Cell {
     private final boolean isAlive;

     Cell(final boolean isAlive) {
       this.isAlive = isAlive;
     }

     public Cell mutate(int neighbors) {
       if (neighbors &lt; 2 &amp;&amp; neighbors &gt; 3) {
         return new Cell(false);
       } else if (this.isAlive || (!this.isAlive &amp;&amp; neighbors == 3)) {
         return new Cell(true);
       } else {
         return new Cell(false);
       }
     }
    }";

    class DeadCell implements Cell {
      public Cell mutate(int neighbors) {
        if (neighbors == 3) {
          return new LivingCell();
        } else {
          return new DeadCell();
      }
    }
        */

    #[test]
    fn submit_draft_successfully() {
        let code = "class Cell {";
    }
}