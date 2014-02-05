package bookings;

public class SeatReservationDemo {

    public static void main(String[] args){
    	
    	/* A simple main method content, only to allocate four seats
    	Seat seats[] = {new Seat('A', 12), new Seat('B', 9), new Seat('F', 17), new Seat('G', 20)};
    	Customer cus = new Customer();
    	SeatReservationManager theManager = new SeatReservationManager();
    	for(int i=0; i<seats.length; i++) {
			try {
				theManager.reserve(seats[i], cus);
			} catch (ReservationException e) {}
		}
    	*/
    	
    	SeatReservationManager theManager = new SeatReservationManager();
    	Customer cus_one = new Customer();
    	Customer cus_two = new Customer();
    	Seat seats[] =new Seat[70];
    	int counter = 0;
    	
    	for (char m='A'; m<='G'; m++) {
    			for (int n=1; n<=20; n+=2) {
    					seats[counter] = new Seat(m, n);
    					try{
    						theManager.reserve(seats[counter], cus_one);
    						theManager.toString();
    						theManager.isReserved(seats[counter]);
    						theManager.unreserve(seats[counter]);
    						theManager.isReserved(seats[counter++]);
    						if(counter%2==0)
    							theManager.reserveNextFree(cus_one);
    						else theManager.reserveNextFree(cus_two);
    					} catch (ReservationException e){}
        		}
    	}
    }
}