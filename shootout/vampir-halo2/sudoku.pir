/* An implementation of standard arithmetic logic unit operations in vampir. Run
   as follows:
   vamp-ir setup params.pp
   vamp-ir compile tests/alu.pir params.pp circuit.plonk
   vamp-ir prove circuit.plonk params.pp proof.plonk
   vamp-ir verify circuit.plonk params.pp proof.plonk
*/

// Ensure that the given argument is 1 or 0, and returns it
def bool x = { x*(x-1) = 0; x };

def sudoku = (7:6:0:5:3:8:1:2:4:[]):
             (2:4:3:7:1:0:6:5:8:[]):
             (8:5:1:4:6:2:0:7:3:[]):
             (4:8:6:0:7:5:3:1:2:[]):
             (5:3:7:6:2:1:4:8:0:[]):
             (1:0:2:8:4:3:7:6:5:[]):
             (6:1:8:3:5:4:2:0:7:[]):
             (0:7:4:2:8:6:5:3:1:[]):
             (3:2:5:1:0:7:8:4:6:[]):
             [];

def hd (h:t) = h;
def tl (h:t) = t;
def nth l n = hd (iter n tl l);

def plus x y = x + y;
def sum l = fold l plus 0;

def check_36 a = {
    36 = sum a
};

// Check rows
def plus x y = x + y;
def sum l = fold l plus 0;

check_36 (nth sudoku 0);
check_36 (nth sudoku 1);
check_36 (nth sudoku 2);
check_36 (nth sudoku 3);
check_36 (nth sudoku 4);
check_36 (nth sudoku 5);
check_36 (nth sudoku 6);
check_36 (nth sudoku 7);
check_36 (nth sudoku 8);

// Check columns
def column sudoku n = {
    (nth (nth sudoku 0) n:
     nth (nth sudoku 1) n:
     nth (nth sudoku 2) n:
     nth (nth sudoku 3) n:
     nth (nth sudoku 4) n:
     nth (nth sudoku 5) n:
     nth (nth sudoku 6) n:
     nth (nth sudoku 7) n:
     nth (nth sudoku 8) n:
     [])
};

check_36 (column sudoku 0);
check_36 (column sudoku 1);
check_36 (column sudoku 2);
check_36 (column sudoku 3);
check_36 (column sudoku 4);
check_36 (column sudoku 5);
check_36 (column sudoku 6);
check_36 (column sudoku 7);
check_36 (column sudoku 8);

// Check sub-sections
def subsection la lb lc n = {
    (nth la (n*3):nth la (n*3+1):nth la (n*3+2):
     nth lb (n*3):nth lb (n*3+1):nth lb (n*3+2):
     nth lc (n*3):nth lc (n*3+1):nth lc (n*3+2):
     [])
};

check_36 (subsection (nth sudoku 0) (nth sudoku 1) (nth sudoku 2) 0);
check_36 (subsection (nth sudoku 0) (nth sudoku 1) (nth sudoku 2) 1);
check_36 (subsection (nth sudoku 0) (nth sudoku 1) (nth sudoku 2) 2);
check_36 (subsection (nth sudoku 3) (nth sudoku 4) (nth sudoku 5) 0);
check_36 (subsection (nth sudoku 3) (nth sudoku 4) (nth sudoku 5) 1);
check_36 (subsection (nth sudoku 3) (nth sudoku 4) (nth sudoku 5) 2);
check_36 (subsection (nth sudoku 6) (nth sudoku 7) (nth sudoku 8) 0);
check_36 (subsection (nth sudoku 6) (nth sudoku 7) (nth sudoku 8) 1);
check_36 (subsection (nth sudoku 6) (nth sudoku 7) (nth sudoku 8) 2);