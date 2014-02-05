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
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }

    //@ ensures \result >= MIN_ROW && \result <= MAX_ROW;
    //@ ensures \result == \old(this.row);
    //@ ensures \result == this.row;
    //@ ensures this.number == \old(this.number);
    public final char getRow() {
        return row;
    }

    //@ ensures \result >= MIN_NUMBER && \result <= MAX_NUMBER;
    //@ ensures \result == \old(this.number);
    //@ ensures \result == this.number;
    //@ ensures this.row == \old(this.row);
    public final int getNumber() {
        return number;
    }

}
