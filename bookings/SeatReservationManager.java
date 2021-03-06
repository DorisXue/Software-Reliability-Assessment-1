package bookings;

public class SeatReservationManager {

	/*@ invariant seatReservations != null;
	    invariant (\forall int x; 0<=x && x<seatReservations.length ==> seatReservations[x]!= null);
	    invariant (\forall int x; 0<=x && x<seatReservations.length ==> \elemtype(\typeof(seatReservations[x])) == \type(Customer));
	    invariant seatReservations.length == (Seat.MAX_ROW-Seat.MIN_ROW)+1;
        invariant (\forall int x; 0<=x && x<seatReservations.length ==> seatReservations[x].length == Seat.MAX_NUMBER);
	@*/
	
    private final Customer[][] seatReservations;
    
    // the size is unknown before declaring a new array, so it will not be affected by 'index too big' warning
    public SeatReservationManager() {
        seatReservations = new Customer[rowToIndex(Seat.MAX_ROW) + 1]
                                       [numberToIndex(Seat.MAX_NUMBER) + 1];
    }

    /*@ requires s != null;
        ensures this.seatReservations == \old(this.seatReservations);
        ensures (\forall int x; 0<=x && x<seatReservations.length ==> this.seatReservations[x] == \old(this.seatReservations)[x]);
    @*/
    public boolean isReserved(Seat s) {
        return seatReservations[rowToIndex(s.getRow())]
                               [numberToIndex(s.getNumber())] != null;
    }

    //@ requires s != null && c != null;
    public void reserve(Seat s, Customer c) 
            throws ReservationException {
        if(isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                        [numberToIndex(s.getNumber())] = c;
    }
    
    //@ requires s != null;
    public void unreserve(Seat s)
            throws ReservationException {
        if(!isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                        [numberToIndex(s.getNumber())] = null;
    }

    //@ requires c != null;
    public void reserveNextFree(Customer c) throws ReservationException {
        for(int rowIndex = 0; rowIndex < seatReservations.length; rowIndex++) {
            for(int numberIndex = 0; 
                    numberIndex < seatReservations[rowIndex].length; 
                    numberIndex++) {
                Seat current = new Seat(indexToRow(rowIndex), 
                    indexToNumber(numberIndex));
                if(!isReserved(current)) {
                    reserve(current, c);
                    return;
                }
            }
        }
        throw new ReservationException();
    }
    
    /*@ ghost String toStringResult; in privateState;
        represents theString <- toStringResult;
        ensures this.seatReservations == \old(this.seatReservations);
        ensures (\forall int x; 0<=x && x<seatReservations.length ==> this.seatReservations[x] == \old(this.seatReservations)[x]);
    @*/
    public String toString() {
        String result = " ";
        
        for(int numberIndex = 0; numberIndex < seatReservations[0].length; 
                numberIndex++) {
            result += " " + indexToNumber(numberIndex);
        }
        result += "\n";

        for(int rowIndex = 0;
            rowIndex < seatReservations.length;
            rowIndex++) {
            result += indexToRow(rowIndex);
            for(int numberIndex = 0; numberIndex < 
                    seatReservations[rowIndex].length; numberIndex++) {
                for(int j = numberIndex; j >= 10; j /= 10) {
                    result += " ";
                }
                result += " " + (isReserved(new Seat(indexToRow(rowIndex), 
                    indexToNumber(numberIndex))) ? "X" : " ");
            }
            result += "\n";
        }
        
        //@ set toStringResult = result;
        return result;
    }

    /*@ requires row >= Seat.MIN_ROW && row <= Seat.MAX_ROW;
        ensures \result >= 0 && \result <= (Seat.MAX_ROW-Seat.MIN_ROW);
        modifies \nothing;
    @*/
    // the situation(precondition) to invoke 'rowtoindex' is not clear; may be invoked by different methods
    private /*@ helper @*/ static int rowToIndex(char row) {
        return row - Seat.MIN_ROW;
    }

    /*@ requires number >= Seat.MIN_NUMBER && number <= Seat.MAX_NUMBER;
        ensures \result >= 0 && \result <= (Seat.MAX_NUMBER-Seat.MIN_NUMBER);
        modifies \nothing;
    @*/
    // the situation(postcondition) to invoke 'rowtoindex' is not clear; may be invoked by different methods
    private /*@ helper @*/ static int numberToIndex(int number) {
        return number - Seat.MIN_NUMBER;
    }
    
    /*@ requires index >= 0 && index <= (Seat.MAX_ROW-Seat.MIN_ROW);
        ensures \result >= Seat.MIN_ROW && \result <= Seat.MAX_ROW;
        modifies \nothing;
    @*/
    private static char indexToRow(int index) {
        return (char)(Seat.MIN_ROW + index);
    }

    /*@ requires index >= 0 && index <= (Seat.MAX_NUMBER-Seat.MIN_NUMBER);
        ensures \result >= Seat.MIN_NUMBER && \result <= Seat.MAX_NUMBER;
        modifies \nothing;
    @*/
    private static int indexToNumber(int index) {
        return index + Seat.MIN_NUMBER;
    }
    
}
