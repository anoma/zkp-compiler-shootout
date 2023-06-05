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

// Get the sum of elements of a list
def plus x y = x + y;
def sum l = fold l plus 0;

// Verify rows
def check_36 a = {
    36 = sum a
};

// Map a function to a list
def map_rec f x acc = (f x):acc;
def map f xs = fold xs (map_rec f) [];

map check_36 sudoku;

//Verify columns
def hd (h:t) = h; // Gets first element
def tl (h:t) = t; // Gets rest of the list
def nth l n = hd (iter n tl l);

def get_item n x y= (nth x n):y;
def get_column a j = fold a (get_item j) [];

def check_columns i = {
    check_36 (get_column sudoku i);
    (i+1)
};
iter 9 check_columns 0;

// Take first n elements of list
def take_rec take (h:t) = h:(take t);
def take n = iter n take_rec (fun x {[]});

def get_slice b e l = take (e-b) (iter b tl l);

// Append two lists together
def cons x y = x:y;
def append xs l = fold xs cons l;

def get_subsection x y matr = {
    def rows = get_slice (x*3) ((x+1)*3) matr;
    def get_3 b e j k = append (get_slice b e j) (k);
    fold rows (get_3 (y*3) (y*3+3)) []
};

def check_subsection i = {
    check_36 (get_subsection i 0 sudoku);
    check_36 (get_subsection i 1 sudoku);
    check_36 (get_subsection i 2 sudoku);
    (i+1)
};
iter 3 check_subsection 0;