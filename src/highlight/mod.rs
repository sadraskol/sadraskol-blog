use crate::highlight::java::Code;

pub mod java;

pub fn parse(_input: &str) -> Code {
    return vec![];
}

#[cfg(test)]
mod test {
    use crate::highlight::java::Token::{Keyword, Literal};
    use crate::highlight::parse;

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

        assert_eq!(vec![
            Keyword("class"),
            Literal(" Cell {")
        ], parse(code));
    }
}