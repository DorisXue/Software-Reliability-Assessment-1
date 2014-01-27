package bookings;

public class Seat {
	
	//@ invariant row >= MIN_ROW && row <= MAX_ROW;
	//@ invariant number >= MIN_NUMBER && number <= MAX_NUMBER;
	
    public static final char MIN_ROW = 'A';
    public static final char MAX_ROW = 'G';
    public static final int MIN_NUMBER = 1;
    public static final int MAX_NUMBER = 20;

    private final char row;
    private final int number;
    
    //@ requires row >= MIN_ROW && row <= MAX_ROW && number >= MIN_NUMBER && number <= MAX_NUMBER;
    //@ modifies this.row;
    //@ modifies this.number;
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }

    //@ ensures \result >= MIN_ROW && \result <= MAX_ROW;
  //@ modifies \nothing;
    public final char getRow() {
        return row;
    }

    //@ ensures \result >= MIN_NUMBER && \result <= MAX_NUMBER;
  //@ modifies \nothing;
    public final int getNumber() {
        return number;
    }

}
