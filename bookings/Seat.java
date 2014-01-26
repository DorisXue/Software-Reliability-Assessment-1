package bookings;

public class Seat {
	
    public static final char MIN_ROW = 'A';
    public static final char MAX_ROW = 'G';
    public static final int MIN_NUMBER = 1;
    public static final int MAX_NUMBER = 20;

    private final char row;
    private final int number;
    
    //@ requires row >= MIN_ROW
    //@ requires number >= MIN_NUMBER
    //@ ensures row >= MIN_ROW
    //@ ensures number >= MIN_NUMBER
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }

    // requires row >= MIN_ROW;
    // ensures \result >= MIN_ROW;
    //@ ensures (row >= MIN_ROW && row <= MAX_ROW) ==> (\result >= MIN_ROW && \result <= MAX_ROW)
    public final char getRow() {
        return row;
    }

    //@ ensures (number >= MIN_NUMBER && number <= MAX_NUMBER) ==> (\result >= MIN_NUMBER && \result <= MAX_NUMBER)
    public final int getNumber() {
        return number;
    }

}
