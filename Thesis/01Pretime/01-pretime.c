
/* Author: Alejandro Flores
 * Dashboard Traffic Light System
 * UNM ECE Thesis
 * Spring 2016
 * Modified: 4/18/16
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>
#include <pthread.h>
#include <assert.h>
#include <sys/time.h>
#include <limits.h>
#include <string.h>

//This code used for debuggin purposes.  To run in production mode, comment out the #define Trace
//#define TRACE
#ifdef TRACE
#define tprintf(...) fprintf(stderr, __VA_ARGS__)
#else
#define tprintf(...)
#endif

// Math function to produce poisson distribution based on mean
int RandPoisson(double mean) {
    double limit = exp(-mean), product = ((double)rand()/INT_MAX);
    int count=0;
    for (; product > limit; count++)
        product *= ((double)rand()/INT_MAX);
    return count;
}

//****************************************************************
// Auotmobile Dashboard
//****************************************************************
typedef enum {true=1, false=0} Bool;
typedef enum {East=0, South=1, West=2, North=3} Direction;
typedef enum {V=0, B=1} Type;
typedef enum {Straight=0, Left=1, Right=2, Uturn=3} Turn;
typedef struct {int carID, schedT,rschedT,arrivT,deptT, from, to,lane, turn, speed, type, t2p,entime,extime,deltat,firstv,lastv; float dist,eta,etd,wait;} DTVehicle;
typedef struct {int dirID, arrvNum, arrvNext, arrvMaxT, arrvMinT; double arrvMeanT; pthread_t arrv_tid, pass_tid;} DTDirection;
typedef struct {int count,speed;} DTLane;
typedef struct {int count;float w;} DTWait;
struct Node { DTVehicle *data;struct Node *next; };
typedef struct { struct Node *front, *rear; int len; pthread_mutex_t L;} DTQueue;


char strDir[4] = {'E','S','W','N'};
char strTurn[4] = {'S','L','R','U'};
char strType[2] = {'V','B'};

int MAXQLEN=199;
#define MAXTIC 3600*24  // Seconds per day
#define VOID   -4
#define PASSED -3
#define RED    -2
#define EMPTY  -1

//*************************
//    Global Variables    *
//*************************
FILE * f1;
FILE * f2;
FILE * f3;
FILE * f4;
FILE * fl;
FILE * fsr;
FILE *d0, *d1, *d2 , *d3;
//Used to read parameter file
char outputpath[7][100];
int m;

//Used for platoons
int Lane_Switch[8];
int placount[8];
int plasum[8];
int plamax[8];
int platotal[8];
int plastart[8];
int plaend[8];
int plaTmax[8];
int plaTimetotal[8];
int plaTimesum[8];
int laneTotal[8];

//Variables for stats
int wtd[4];   //Wait per direction
float maxwt = 0;  //max wait time
int vstop = 0;  //Count Vehicles that had to stop
int errors = 0;
int count_vehicles = 0;
int count_busses = 0;
int wait_sum= 0;
int  nDetour=0, nPass=0, nArrv=0, nResidue=0;
int allvehicles = 0;
//int trigger;
//int ON;
int acount =0 ,bcount = 0 , ccount=0,dcount=0,ecount=0,fcount=0,gcount=0,hcount=0;
int asum = 0, bsum = 0, csum = 0, dsum =0, esum=0, fsum=0, gsum =0, hsum =0;
int anext = 0,bnext = 0,cnext = 0,dnext = 0,enext = 0,fnext = 0,gnext = 0,hnext = 0;

////Variable used for lazy scheduling
//int ewcount = 0;
//int nscount = 0;
//int ewflush = 0;
//int nsflush = 0;

//int ecount = 0;
//int eflush = 0;
//int scount = 0;
//int sflush = 0;
//int wcount = 0;
//int wflush = 0;
//int ncount = 0;
//int nflush = 0;


//DTVehicle *espot[500];
//DTVehicle *sspot[500];
//DTVehicle *wspot[500];
//DTVehicle *nspot[500];

//int vQ, EWT,NST ,nsTcount, ewTcount ;
DTVehicle *ewspot[500];
DTVehicle *nsspot[500];
int enable;
int T2P;
double SCount = 0;
float IntTimer, nsturn,ns,ewturn ,ew;
float nsturnper,nsper,ewturnper,ewper;

int perVRight;
int perVLeft;
int perBuses;
double lane4_waitsum = 0;
int lane4_count = 0;

//parameter Variables
double mean0,mean1,mean2,mean3;
int vClk, timers; // 3600 sec - could use integer since it's 24 hrs as max, default one hour
double mean, starttime;
int sp_low_bound, sp_upper_bound, com_dist;

//Lanes
DTLane Lane[4][8];

//Queues
DTQueue QSR[4], QL[4];

//Arrays
int L[4][MAXTIC];
int S[4][MAXTIC];
int R[4][MAXTIC];

// L_last points to the latest time slot we can schedule, after that all empty
int S_last_tslot[4], S_first_tslot[4], R_last_tslot[4], R_first_tslot[4] , L_last_tslot[4], L_first_tslot[4];

// bookkeeping of performance data, accumulated total sum for avg later on, counting number, max
typedef struct {int num,nums,numr,numl, waitsum; float waitmax;} DTPerfData;
DTPerfData vstat[4], road[4];

int gID = 0;
DTDirection DirArray[4]; //Initialize array of type DTDirection

//TODO Work on figuring out what C does
// at the particular time slot, the number of cars occupy the intersection
int C[MAXTIC];


//******************************
//       Program Functions
//******************************

//Function related to queueing an dequeuing
void Enqueue(DTQueue *ptrQ,DTVehicle *ptrCar) {

    //Create a new NODE
    struct Node* temp = (struct Node*)malloc(sizeof(struct Node));
    //tprintf("Temp Address: %p \n",temp);

    //Check for lack of memory
    if (!temp){
        //tprintf("No enough memory!\n");
        //return 0;
    }
    else{
        //Save Data and NUll to new Node
        temp->data = ptrCar;
        temp->next = NULL;

        // Only touch 'front' if this is the first item
        if (ptrQ->front == NULL) {
            ptrQ->front = temp;
            //tprintf("New Front of Queue! \n");
        }

        // You always have to touch 'rear'
        if (ptrQ->rear != NULL){
            ptrQ->rear->next = temp;
            ptrQ->rear = temp;
            ptrQ->len += 1;
            //tprintf("New Rear of Queue! \n");
        }
        else {
            ptrQ->rear = temp;
            ptrQ->len += 1;
            //tprintf("First Item in Queue! \n");
        }
    }
    //return (1);
}
DTVehicle* Dequeue(DTQueue *ptrQ) {

    //Save current front to temp
    struct Node *temp = ptrQ->front;

    if (ptrQ->front == NULL){
        //return 0;
        //tprintf("Error, nothing on the queue!!");
    }
    else {
        //If there is nothing left in the queue, change front and rear to NUll
        if (ptrQ->front == ptrQ->rear) {
            //tprintf("Front = Rear DR. Lee! \n");
            ptrQ->front = ptrQ->rear = NULL;
            ptrQ->len = 0;
            //Print Error if case len is not zero (Might want to use an Assert Statement)
        }
        else {
            //Make the next node the front
            //tprintf("Removing: %d",ptrQ->front->data->carID);
            ptrQ->front = ptrQ->front->next;
            ptrQ->len -= 1;
        }
    }
    return temp->data;
}
DTVehicle* QueueTop(DTQueue *ptrQ) {
    DTVehicle *cPtr;

    //if the Queue is not empty the front of the Queue is returned
    if (ptrQ->len == 0) return NULL;
    else {
        //Return the pointer of the actual data
        cPtr = ptrQ->front->data;
        return cPtr;
    }
}
int QueueLen(DTQueue *ptrQ) {
    //DTVehicle *cPtr;
    int Qlen;

    //if the Queue is not empty the front of the Queue is returned
    if (ptrQ->len == 0) return 0;
    else {
        //Return the pointer of the actual data
        //cPtr = ptrQ->front->data;
        Qlen = ptrQ->len;
        return ptrQ->len;
    }
}
void QueueInit(DTQueue *ptrQ) { // the Queue is initialized to be empty
    ptrQ->front = NULL;
    ptrQ->len = 0;
    ptrQ->rear = NULL;     // circular Q, FIFO
    pthread_mutex_init(&ptrQ->L,NULL);
}

// Virtual Clock for simulation
int SetVClk(int hrs, int mins, int secs) {
    assert(secs<60 && secs>=0); assert(mins<60 && mins>=0); assert(hrs<24 && hrs>=0);
    int t = hrs*3600 + mins*60 + secs;
    return(t);
}
void PrintVClk(int c) {
    int hrs,mins,secs;
    secs = c%60; c-=secs;
    mins = c%3600; c-=mins; mins/=60;
    hrs = c/3600;
    printf("%02d:%02d:%02d",hrs,mins,secs);
}
void InitCross(int maxTic) {
    assert(maxTic<=MAXTIC);
    int i,z;
    for (i=0; i<maxTic; i++) { // initially, EMPTY means nothing reserved, available
        S[0][i] = S[1][i] = S[2][i] = S[3][i] = EMPTY;  //Empty = -1
        R[0][i] = R[1][i] = R[2][i] = R[3][i] = EMPTY;
        L[0][i] = L[1][i] = L[2][i] = L[3][i] = EMPTY;
        C[i]  = 0;
    }

    //WIll need to loop this!!!
    //spotdir[0] = spotdir[1] = spotdir[2] = spotdir[3] = 0;
    for (i=0; i<=20;i++){
        nsspot[i]=0;
        ewspot[i]=0;
    }


    //Initialize lane ,speed arrray, and output next count
    for (i=0; i<4; i++) {
        for (z=0; z<4; z++)
            Lane[i][z].count = Lane[i][z].speed = 0;
    }


    for (i=0; i<8; i++){
        Lane_Switch[i] = 0;
        placount[i] = 0;
        plasum[i] = 0;
        plamax[i] =0;
        platotal[i] = 0;
        plastart[i] = 0;
        plaend[i] = 0;
        plaTmax[i] = 0;
        plaTimetotal[i] = 0;
        plaTimesum[i] = 0;
        laneTotal[i] = 0;
    }

    for (i=0; i<4; i++) {
        S_last_tslot[i] = L_last_tslot[i] = R_last_tslot[i] = 0;
        //S_first_tslot[i] = L_first_tslot[i] = R_first_tslot[i] = 0;
    }
}

//These function are used for time slot blocking
void setL2Red(int d, int i) {
    L[d][i] = RED;
    L_last_tslot[d] = (i > L_last_tslot[d]) ? i : L_last_tslot[d];

}
void setS2Red(int d, int i) {
    S[d][i] = RED;
    S_last_tslot[d] = (i > S_last_tslot[d]) ? i : S_last_tslot[d];
}
void setSR2Red(int d, int i) {
    S[d][i] = R[d][i] = RED;
    //Adjust straight last_slot
    S_last_tslot[d] = (i > S_last_tslot[d]) ? i : S_last_tslot[d];
    //Adjust right last_slot
    R_last_tslot[d] = (i > R_last_tslot[d]) ? i : R_last_tslot[d];

}

//This function help identify what lane the vehicle is arrving from
int IdentifyLane(int d, int to){

    int lane;
    //Determine the line the vehicle is in based in the to and from direction
    if (d == 0 && to == Left) {
        lane = 1;
    }
    else if (d == 0 && (to == Right || to == Straight)){
        lane = 0;
    }


    if (d == 1 && to == Left) {
        lane = 3;
    }
    else if (d == 1 && (to == Right || to == Straight)){
        lane = 2;
    }


    if (d == 2 && to == Left) {
        lane = 5;
    }
    else if (d == 2 && (to == Right || to == Straight)){
        lane = 4;
    }


    if (d == 3 && to == Left) {
        lane = 7;
    }
    else if (d == 3 && (to == Right || to == Straight)){
        lane = 6;
    }

    return lane;
}

//Used to determine when to terminate a platton based on a conflicting vehicle
void conflict(int d,int to,int lane,int clk){
    int l1,l2,l3,l4,i;

    for (i=0; i<8; i++){
        if (plasum[i] > plamax[i]){
            plamax[i] = plasum[i];
        }

        if (plaTimetotal[i] > plaTmax[i]){
            plaTmax[i] = plaTimetotal[i];
        }
    }

    if (to == Left){

        l1 = (lane + 1) % 8;  //Straight
        l2 = (lane + 2) % 8;  //Left
        l3 = (lane + 3) % 8;  //Straight
        l4 = (lane + 6) % 8;  //Left

        if(plasum[l1] >0 ){fprintf(fsr,"%d,%d\n",l1,plasum[l1]);}
        if(plasum[l2] >0 )fprintf(fl,"%d,%d\n",l2,plasum[l2]);
        if(plasum[l3] >0 )fprintf(fsr,"%d,%d\n",l3,plasum[l3]);
        if(plasum[l4] >0 )fprintf(fl,"%d,%d\n",l4,plasum[l4]);

        //End of Platoon for the following lane
        Lane_Switch[l1] = 0;
        Lane_Switch[l2] = 0;
        Lane_Switch[l3] = 0;
        Lane_Switch[l4] = 0;

        plasum[l1] = 0;
        plasum[l2] = 0;
        plasum[l3] = 0;
        plasum[l4] = 0;

        plaTimetotal[l1] = 0;
        plaTimetotal[l2] = 0;
        plaTimetotal[l3] = 0;
        plaTimetotal[l4] = 0;

    }

    if (to == Straight){
        l1 = (lane + 2) % 8;  //Straight
        l2 = (lane + 5) % 8;  //Left
        l3 = (lane + 6) % 8;  //Straight
        l4 = (lane + 7) % 8;  //Left


        if(plasum[l1] >0 ){fprintf(fsr,"%d,%d\n",l1,plasum[l1]);}
        if(plasum[l2] >0 )fprintf(fl,"%d,%d\n",l2,plasum[l2]);
        if(plasum[l3] >0 )fprintf(fsr,"%d,%d\n",l3,plasum[l3]);
        if(plasum[l4] >0 )fprintf(fl,"%d,%d\n",l4,plasum[l4]);


        //End of Platoon for the following lane
        Lane_Switch[l1] = 0;
        Lane_Switch[l2] = 0;
        Lane_Switch[l3] = 0;
        Lane_Switch[l4] = 0;

        plasum[l1] = 0;
        plasum[l2] = 0;
        plasum[l3] = 0;
        plasum[l4] = 0;

        plaTimetotal[l1] = 0;
        plaTimetotal[l2] = 0;
        plaTimetotal[l3] = 0;
        plaTimetotal[l4] = 0;

    }

    if(to == Right){
        l1 = (lane + 2) % 8; //Straight
        //Used to create histogram
        if (plasum[l1] >0 ){fprintf(fsr,"%d,%d\n",l1,plasum[l1]);}

        //End of Platoon for the following lane
        Lane_Switch[l1] = 0;
        plasum[l1] = 0;
        plaTimetotal[l1] = 0;
    }
}

DTVehicle *CarNew(int d, int k) {
    DTVehicle *newptr;
    int e,mph,lane,vl;
    double msec = 0;
    float arrivT;


    newptr = (DTVehicle*)malloc(sizeof(DTVehicle));
    newptr->from = d;
    newptr->deptT = 0;

    newptr->to=Straight; // 60% Go Straight
    if ((e=rand()%100)<perVRight) {
        newptr->to = Right; // 20% turn left
    }
    vl = 100-perVLeft;
    if (e>=vl) {
        newptr->to = Left;// 20% turn right
    }

    lane = IdentifyLane(d,newptr->to);

    mph = (rand() % (sp_upper_bound+1-sp_low_bound))+sp_low_bound; // (Max+1-Min)+Min

    //Match MPH of last vehicle if lane is not empty
    if (Lane[d][lane].count > 0 && mph > Lane[d][lane].speed) {
        mph = Lane[d][lane].speed;
    }

    msec = (mph * .44704);  //convert mph to meters/sec
    arrivT = round(com_dist/msec);

    //Vehicle Type Sedan= 0 Trailers & Busses = 1
    newptr->type = 0;
    if ((rand()%100)<perBuses) {
        newptr->type = 1; // 20% are busses
    }

    newptr->lane = lane;
    newptr->carID = ++gID;
    newptr->speed = mph;
    newptr->dist = com_dist;
    newptr->eta = k + arrivT;
    newptr->arrivT = arrivT;
    newptr->schedT = 0;
    newptr->wait = 0;
    newptr->firstv = 0;
    newptr->lastv = 0;


    nArrv++; // total number arrival of cars


    //Vehicles are added to the queue
    if (newptr->to==Left) {
        tprintf("Adding Car to QL Vehicle: %d From: %d \n",newptr->carID,d);
        Enqueue(&QL[d], newptr); // Vehicle added to queue
        Lane[d][lane].count += 1;  //Increase the count on vehicles in the lane
        Lane[d][lane].speed = newptr->speed;  //This is in mph
    }
    else {
        tprintf("Adding Car to QSR Vehicle: %d From: %d \n",newptr->carID,d);
        Enqueue(&QSR[d], newptr); //Vehicle added to queue
        Lane[d][lane].count += 1;
        Lane[d][lane].speed = newptr->speed;  //This is in mph
    }
    return (newptr);
}

//Prints the vehicles that are arriving
void CarPrint(DTVehicle *cptr,int clk) {
    printf("*******************************************************************************************************************************************************\n");
    printf("%d:vID Type:%c T2P: %d From:%c Going:%c Lane:%d Speed:%d mph Distance:%.2f meters Tic:%d ArrvT: %d ETA:%.0f sec SchedT: %d  ETD:%.0f  Waiting: %.0lf \n",
           cptr->carID,strType[cptr->type], cptr->t2p, strDir[cptr->from], strTurn[cptr->to],cptr->lane, cptr->speed, cptr->dist,clk,cptr->arrivT, cptr->eta,cptr->schedT, cptr->etd,cptr->wait);
    printf("********************************************************************************************************************************************************\n\n");
}

//Prints the vehicles that are passing
void CarPrintOut(DTVehicle *cptr,int clk) {

    printf("*******************************************************************************************************************************************************\n");
    printf("                                                                            ****Passing From %c To: %c ***** \n",strDir[cptr->from],strTurn[cptr->to]);
    printf("%d:vID Tic:%d T2P: %d From:%c Going:%c Lane:%d Speed:%d mph Distance:%.2f meters ArrvT: %d ETA:%.0f sec SchedT: %d RSchedT:%d  ETD:%.0f  Waiting: %.0lf \n",
           cptr->carID,clk, cptr->t2p, strDir[cptr->from], strTurn[cptr->to],cptr->lane, cptr->speed, cptr->dist,cptr->arrivT, cptr->eta,cptr->schedT, cptr->rschedT, cptr->etd,cptr->wait);
    printf("********************************************************************************************************************************************************\n\n");

    //fprintf(f,"%d,%.0f,%.0f,%c,%d,%c,%d,%d\n",cptr->carID,cptr->eta,cptr->etd,strDir[cptr->from],strTurn[cptr->to],cptr->wait,cptr->t2p,cptr->schedT);
    //fprintf(f1,"%d,%f,%f,%d,%c,%f,%d,%d\n",cptr->carID,cptr->eta,cptr->etd,strDir[cptr->from],strTurn[cptr->to],cptr->wait,cptr->t2p,cptr->schedT);

}

//Determines the time to pass for each vehicle
int t2p(int schedT, int type, int to, int ETA){
    int time2pass = 0;

    //Set time it take to cross intersection for cars
    if (schedT == ETA && type == 0 && T2P == 1){  //Vehicle is in motion
        if (to == Left){
            time2pass = 3; //3
        }
        if (to == Straight){
            time2pass = 2; //2
        }
        if (to == Right){
            time2pass = 1; //1
        }
    }
    else if (schedT > ETA && type == 0 && T2P == 1){   //vehicle is at rest
        if (to == Left){
            time2pass = 4; //4
        }
        if (to == Straight){
            time2pass = 3;  //3
        }
        if (to == Right){
            time2pass = 2;  //2
        }
    }

    //Set time it takes to cross intersection for trailers and busses
    if (schedT == ETA && type == 1  && T2P == 1){ //Vehicle is in motion
        if (to == Left){
            time2pass = 4;  //4
        }
        if (to == Straight){
            time2pass = 3;  //3
        }
        if (to == Right){
            time2pass = 2;  //2
        }
    }
    else if (schedT > ETA && type == 1 && T2P == 1){ //vehicle is at rest
        if (to == Left){
            time2pass = 5;  //5
        }
        if (to == Straight){
            time2pass = 4;  //4
        }
        if (to == Right){
            time2pass = 3; //3
        }
    }

    if (T2P == 0){
        time2pass = 1;
        if (type == 0){
            time2pass = 1;
        }
        if (type == 1){
            time2pass = 2;
        }
    }


    return(time2pass);
}

//Determines the time to pass for vehicles in a platoon
int t2pp(int type, int to){
    int time2pass = 0;

    if (type == 0 ){   //vehicle is at rest
        if (to == Left){
            time2pass = 4; //4
        }
        if (to == Straight){
            time2pass = 3;  //3
        }
        if (to == Right){
            time2pass = 2;  //2
        }
    }

    if (type == 1){ //vehicle is at rest
        if (to == Left){
            time2pass = 5;  //5
        }
        if (to == Straight){
            time2pass = 4;  //4
        }
        if (to == Right){
            time2pass = 3; //3
        }
    }

    return(time2pass);
}

//Does all the vehicle scheduling
void SchedCross(DTVehicle *pCar, int clk) {
    int id = pCar->carID;
    int to = pCar->to;
    int from = pCar->from;
    int ETA = pCar->eta;
    int ETD = pCar->etd;
    int delay = pCar->deltat;
    int lane = pCar->lane;
    int x, i, j, z, spaces, WaitTime;
    int carptr;
    int time2pass = 0;

    //PROCESS vehicles turning left
    if (to == Left) {

        //Add car to the back
        if (ETA > L_last_tslot[from]){  //If vehicle arrival time is after last vehicle
            x= ETA;
        }
        else{
            x= 1 + L_last_tslot[from];  //If not, then time slot is after last vehicle
        }
    }

        //PROCESS vehicles turning right
    else if (to == Right) {
        if (ETA > R_last_tslot[from]){
            x = ETA;
        }
        else{
            x = 1 + R_last_tslot[from];
        }
    }

        //   PROCESS vehicles going straight
    else {
        if (ETA > S_last_tslot[from]){
            x = ETA;
        }
        else {
            x = 1 + S_last_tslot[from];
        }
    }

    pCar->schedT = x;  //This record the time the vehicle actually crossed


    //Set the time it will take the vehicle to pass

    time2pass = t2p(pCar->schedT, pCar->type, pCar->to, ETA);
    pCar->t2p = time2pass;

    //******************************************
    //Calculate waiting time for each vehicle
    //******************************************


    /*********************************************************************************
     *             Block time slot based on calculated time2pass
     *********************************************************************************/
    if (to == Left) {
        for (i = 0; i < time2pass; i++) {                    //Should it be <= or just =
            //If time slot is empty, then write the vID on it.
            if (L[from][x + i] == EMPTY) {
                L[from][x + i] = id;
            }
        }
//        for (i = 0; i < time2pass; i++) {
//            //Now block the time slot in the other arrays
//            setS2Red((from + 1) % 4, x + i);  //printf("Block SR: %d\n",((from + 1) % 8));
//            setL2Red((from + 1) % 4, x + i);   //printf("Block L: %d\n",((from + 1) % 8));
//            setS2Red((from + 2) % 4, x + i);  //printf("Block SR: %d\n",((from + 2) % 8));
//            setL2Red((from + 3) % 4, x + i);   //printf("Block L: %d\n",((from + 3) % 8));
//        }
        // update after scheduling and 3 determine how long it takes for the car takes to cross the intersection
        if (L_last_tslot[from] < (x + time2pass)) {
            L_last_tslot[from] = x + time2pass;
        }

        if (L_first_tslot[from] < (x + time2pass)) {
            L_first_tslot[from] = x + time2pass;
        }

    }


    else if (to == Right) {
        for (i = 0; i < time2pass; i++) {
            if (S[from][x + i] == EMPTY) { S[from][x + i] = VOID; }
            if (R[from][x + i] == EMPTY) { R[from][x + i] = id;}
        }

//        for (i = 0; i < time2pass; i++) {
//            setS2Red((from + 1) % 4, x + i); //printf("Block S: %d\n",((from + 1) % 4));
//        }

        if (R_last_tslot[from] < (x + time2pass)) R_last_tslot[from] = x + time2pass;
        if (R_first_tslot[from] < (x + time2pass)) R_first_tslot[from] = x + time2pass;
        if (S_last_tslot[from] < (x + time2pass)) S_last_tslot[from] = x + time2pass;
        if (S_first_tslot[from] < (x + time2pass)) S_first_tslot[from] = x + time2pass;
    }

    else {
        for (i = 0; i < time2pass; i++) {
            if (S[from][x + i] == EMPTY) { S[from][x + i] = id;}
            if (R[from][x + i] == EMPTY) { R[from][x + i] = VOID; }
        }

//        for (i = 0; i < time2pass; i++) {
//            //Now block the time slot in the other arrays
//            //printf("Blocking Dir:%d  Slot: %d\n",(from + 1) % 4, x+i);
//            setS2Red((from + 1) % 4, x + i);   //printf("Block S: %d\n",((from + 1) % 4));
//            setL2Red((from + 2) % 4, x + i);   //printf("Block L: %d\n",((from + 2) % 4));
//            setSR2Red((from + 3) % 4, x + i);   //printf("Block SR: %d\n",((from + 3) % 4));
//            setL2Red((from + 3) % 4, x + i);   //printf("Block L: %d\n",((from + 3) % 4));
//        }
        if (R_last_tslot[from] < (x + time2pass)) R_last_tslot[from] = x + time2pass;
        if (R_first_tslot[from] < (x + time2pass)) R_first_tslot[from] = x + time2pass;
        if (S_last_tslot[from] < (x + time2pass)) S_last_tslot[from] = x + time2pass;
        if (S_first_tslot[from] < (x + time2pass)) S_first_tslot[from] = x + time2pass;

    }

    pCar->etd = x + time2pass;
    CarPrint(pCar, clk);
}

//This function collect all the statistics after a vehicle passes
void CarPass(DTVehicle *carptr, int clk) { // collect performance data upon the car passed the intersection
    int i,z,d,lane,to;
    float w = 0;

    w = carptr->wait;

    //***************************
    // Find Platoon Information 
    //***************************
    lane = carptr->lane;
    d = carptr->from;
    to = carptr->to;

    plaTimesum[lane] =  plaTimesum[lane] + carptr->t2p; //Keeps a sum of time taken by platoon
    plaTimetotal[lane] =  plaTimetotal[lane]+carptr->t2p; //Keeps track of size of platoon
    platotal[lane]++;  //Keep track of the total amount of vehicles
    plasum[lane]++;  //Count the amount of car per platoon

    for (i = 0; i < 8; i++){
        if (lane == i & Lane_Switch[i] == 0){
            placount[i]++;     // Keeps track of how many platoons got created
            plastart[i]= clk;
            Lane_Switch[i] = 1;
        }
    }

    conflict(d,to,lane,clk);
    //*** End Platoon Info Code
    //***************************


    //***********************
    //  Stats per lane
    laneTotal[lane]++;


    //*****************************
    //   Stats per direction

    //Count the number of cars for each direction
    road[d].num++;  //same as  laneTotal[lane]++;

    //Add vehicle wait per direction
    road[d].waitsum += w;
    //vstat[d].waitsum += w;

    //FInd max wait time per direction
    if (w > road[d].waitmax) {
        road[d].waitmax = w;
    }

    //Total Vehicles passed per direction
    vstat[d].num++;



    //*************************
    //Stats in ALL directions

    //count the total number of vehicles that passed the intersection
    nPass++;

    //sum of waiting time of all vehicles and directions
    //wait_sum += w;

    //calculate longest wait time
    if (w > maxwt){
        maxwt = w;
    }

    //Sum the total vehicles that had to wait in all directions
    if (w>1) {
        //printf("#Waiting");
        vstop++;
    }

    //Print a list of vehicles that passed into the sim file
    fprintf(f1,"%d,%c,%c,%d,%.2f,%.02f,%d,%d,%d,%c,%.2f,%d\n",carptr->carID,strDir[carptr->from],strTurn[carptr->to],carptr->lane,carptr->eta,w,carptr->schedT,carptr->rschedT,carptr->t2p,strType[carptr->type],carptr->etd,clk);

    assert(carptr != NULL);

    //Count vehicles going on each direction
    if (carptr->to == Left) {
        vstat[d].numl++;
    }
    if (carptr->to == Right) {
        vstat[d].numr++;
    }
    if (carptr->to == Straight) {
        vstat[d].nums++;
    }


    //Car= 0 Trailers & Busses = 1
    if (carptr->type == 1 ) {
        count_busses ++;
    }
    if (carptr->type == 0 ){
        count_vehicles ++;
    }


    //Remove vehicle from lane array
    Lane[d][carptr->lane].count --;


//    C[carptr->schedT]++; // adding to the number of cars occupy the intersection
//    C[carptr->schedT + 1]++;
//    C[carptr->schedT + 2]++;

    free(carptr);
    //AT LAST, THE POINTER IS FREE AGAIN!!!


}

//Function used to dispatch vehicles
void HandleCross(int dir, int clk) {
    DTVehicle *carptr;

    if (clk ==1 && dir ==0)  {
        printf("*****Ranges******\n");
        printf("EW Turn: %.0lf - %.0lf\n",SCount,SCount + nsturn);
        printf("EW: %.0lf - %.0lf\n",SCount + nsturn,SCount + (nsturn + ns) );
        printf("NS Turn: %.0lf - %.0lf\n",SCount + (nsturn + ns),(SCount+ ewturn + nsturn + ns));
        printf("NS: %.0lf - %.0lf\n\n",SCount+ ewturn + nsturn + ns, SCount + ew + ewturn + nsturn + ns);
    }

    //********************************************
    //           Step 1 - E/W Turn Left
    //********************************************
    if (SCount <= clk && clk < ( SCount + nsturn)) {
        //printf("EW Left CLK: %d \n",clk);
        if (QueueLen(&QL[0]) > 0 &&  QL[0].front->data->schedT <= clk){
                if (acount == 0) {
                    if (asum <= ewturn - 2) {
                        carptr = Dequeue(&QL[0]);
                        if (carptr->eta < clk){
                            carptr->t2p = t2pp(carptr->type,carptr->to);
                        }
                        asum += carptr->t2p+1;
                        carptr->rschedT = clk +1;
                        carptr->wait = clk + 1 - carptr->eta;
                        carptr->etd = clk +1 + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        anext = clk + carptr->t2p+2;
                    }
                }
                if (acount > 0) {
                    if (anext <= clk) {
                        if (asum <= ewturn-1) {
                            carptr = Dequeue(&QL[0]);
                            //asum += carptr->t2p;
                            if (carptr->type == 0){
                                asum += 1;
                                carptr->t2p = 1;
                            }
                            if (carptr->type == 1){
                                asum += 2;
                                carptr->t2p = 2;
                            }
                            carptr->rschedT = clk;
                            carptr->wait = clk - carptr->eta;
                            carptr->etd = clk + carptr->t2p;
                            wait_sum += carptr->wait;
                            CarPass(carptr, clk);
                            CarPrintOut(carptr, clk);
                            anext = clk + carptr->t2p+1;
                        }
                    }
                }acount++;
            }


        if (QueueLen(&QL[2]) > 0 && QL[2].front->data->schedT <= clk) {
            if (bcount == 0) {
                if (bsum <= ewturn - 2) {
                    carptr = Dequeue(&QL[2]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    bsum += carptr->t2p;
                    carptr->rschedT = clk +1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    bnext = clk + carptr->t2p+2;
                }
            }
            if (bcount > 0) {
                if (bnext <= clk) {
                    if (bsum <= ewturn-1) {
                        carptr = Dequeue(&QL[2]);
                        //bsum += carptr->t2p;
                        if (carptr->type == 0){
                            bsum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            bsum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        bnext = clk + carptr->t2p +1;
                    }
                }
            }bcount++;
        }
    }

    //********************************************
    //      Step 2 - E/W Straight Right
    //********************************************
    if ((SCount + nsturn) <= clk && clk < SCount + (nsturn + ns)) {
        //printf("EW S/R CLK: %d \n",clk);
        if (QueueLen(&QSR[0]) > 0 &&  QSR[0].front->data->schedT <= clk){
            if (ccount == 0) {
                if (csum <= ew - 2) {
                    carptr = Dequeue(&QSR[0]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    csum += carptr->t2p;
                    carptr->rschedT = clk +1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    cnext = clk + carptr->t2p+2;
                }
            }
            if (ccount > 0) {
                if (cnext <= clk) {
                    if (csum <= ew-1) {
                        carptr = Dequeue(&QSR[0]);
                        //csum += carptr->t2p;
                        if (carptr->type == 0){
                            csum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            csum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        cnext = clk + carptr->t2p+1;
                    }
                }
            }ccount++;
        }



        if (QueueLen(&QSR[2]) > 0 &&  QSR[2].front->data->schedT <= clk){
            if (dcount == 0) {
                if (dsum <= ew - 2) {
                    carptr = Dequeue(&QSR[2]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    dsum += carptr->t2p;
                    carptr->rschedT = clk +1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    dnext = clk + carptr->t2p+2;
                }
            }
            if (dcount > 0) {
                if (dnext <= clk) {
                    if (dsum <= ew-1) {
                        carptr = Dequeue(&QSR[2]);
                        //dsum += carptr->t2p;
                        if (carptr->type == 0){
                            dsum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            dsum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        dnext = clk + carptr->t2p+1;
                    }
                }
            } dcount++;
        }
    }



    //********************************************
    //           Step 3 - N/S Turn Left
    //********************************************
    //Green for North/South turning traffic   120 - 150
    if (SCount+ (nsturn + ns) <= clk && clk < (SCount+ ewturn + nsturn + ns)){
        //printf("NS Left CLK: %d \n",clk);
        if (QueueLen(&QL[1]) > 0 &&  QL[1].front->data->schedT <= clk){
            if (ecount == 0) {
                if (esum <= nsturn - 2) {
                    carptr = Dequeue(&QL[1]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    esum += carptr->t2p;
                    carptr->rschedT = clk +1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1+ carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    enext = clk + carptr->t2p+2;
                }
            }
            if (ecount > 0) {
                if (enext <= clk) {
                    if (esum <= nsturn-1) {
                        carptr = Dequeue(&QL[1]);
                        //esum += carptr->t2p;
                        if (carptr->type == 0){
                            esum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            esum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        enext = clk + carptr->t2p+1;
                    }
                }
            }ecount++;
        }


        if (QueueLen(&QL[3]) > 0 &&  QL[3].front->data->schedT <= clk){
            if (fcount == 0) {
                if (fsum <= nsturn - 2) {
                    carptr = Dequeue(&QL[3]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    fsum += carptr->t2p;
                    carptr->rschedT = clk +1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    fnext = clk + carptr->t2p+2;
                }
            }
            if (fcount > 0) {
                if (fnext <= clk) {
                    if (fsum <= nsturn-1) {
                        carptr = Dequeue(&QL[3]);
                        //fsum += carptr->t2p;
                        if (carptr->type == 0){
                            fsum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            fsum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        fnext = clk + carptr->t2p+1;
                    }
                }
            }fcount++;
        }
    }


    //********************************************
    //      Step 4 - N/S Straight Right
    //********************************************
    if ((SCount+ ewturn + nsturn + ns) <= clk && clk < (SCount + ew + ewturn + nsturn + ns)) {
        //printf("NS S/R CLK: %d \n",clk);
        //printf("SchedT: %d \n",QSR[1].front->data->schedT);
        if (QueueLen(&QSR[1]) > 0 &&  QSR[1].front->data->schedT <= clk){
            if (gcount == 0) {
                if (gsum <= ns - 2) {
                    carptr = Dequeue(&QSR[1]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    gsum += carptr->t2p;
                    carptr->rschedT = clk;  //Took 1 off
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    gnext = clk + carptr->t2p+2;
                    printf("Gnext: %d\n",gnext);
                }
            }
            if (gcount > 0) {
                if (gnext <= clk) {
                    if (gsum <= ns-1) {
                        carptr = Dequeue(&QSR[1]);
                        //gsum += carptr->t2p;
                        if (carptr->type == 0){
                            gsum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            gsum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        gnext = clk + carptr->t2p+1;
                    }
                }
            }gcount++;
        }


        if (QueueLen(&QSR[3]) > 0 &&  QSR[3].front->data->schedT <= clk){
            if (hcount == 0) {
                if (hsum <= ns - 2) {
                    carptr = Dequeue(&QSR[3]);
                    if (carptr->eta < clk){
                        carptr->t2p = t2pp(carptr->type,carptr->to);
                    }
                    hsum += carptr->t2p;
                    carptr->rschedT = clk+1;
                    carptr->wait = clk + 1 - carptr->eta;
                    carptr->etd = clk + 1 + carptr->t2p;
                    wait_sum += carptr->wait;
                    CarPass(carptr, clk);
                    CarPrintOut(carptr, clk);
                    hnext = clk + carptr->t2p+2;
                }
            }
            if (hcount > 0) {
                if (hnext == clk) {
                    if (hsum <= ns-1) {
                        carptr = Dequeue(&QSR[3]);
                        //hsum += carptr->t2p;
                        if (carptr->type == 0){
                            hsum += 1;
                            carptr->t2p = 1;
                        }
                        if (carptr->type == 1){
                            hsum += 2;
                            carptr->t2p = 2;
                        }
                        carptr->rschedT = clk;
                        carptr->wait = clk - carptr->eta;
                        carptr->etd = clk + carptr->t2p;
                        wait_sum += carptr->wait;
                        CarPass(carptr, clk);
                        CarPrintOut(carptr, clk);
                        hnext = clk + carptr->t2p+1;
                    }
                }
            }hcount++;
        }
    }

    if (clk == (SCount + (2 * ns) + (2 * nsturn))){
        SCount = (SCount + (2 * ns) + (2 * nsturn));


        asum = 0, bsum = 0,csum = 0,dsum=0,esum=0,fsum=0,gsum=0,hsum=0;
        anext = 0, bnext =0, cnext =0, dnext =0,enext=0,fnext=0,gnext=0,hnext=0;
        acount = 0; bcount =0, ccount=0,dcount=0,ecount=0,fcount=0,gcount=0,hcount=0;

    }
}

long InitTime() {
    struct timeval st;
    gettimeofday(&st, NULL);
    return(starttime = (1000.0*st.tv_sec+st.tv_usec/1000.0));
}

//This function is used to determin when the next vehicle arrives.
//Function depends on DTVehicle *CarNew to come up with a new vehicle
void CarArrive(int dir, int sec) {
    int arrival;
    DTVehicle *newptr;

    if (DirArray[dir].arrvNext <= 0 ) {
        //generate a new vehicle arrival
        arrival = RandPoisson(DirArray[dir].arrvMeanT);

        //printf("ARRIVAL!!: %d\n",arrival);

        //arrvMaxT: max value of interval
        if (arrival > DirArray[dir].arrvMaxT) {
            DirArray[dir].arrvMaxT = arrival;
        }
        if (arrival < DirArray[dir].arrvMinT) {
            DirArray[dir].arrvMinT = arrival;
        }

        //Create new vehicle
        newptr = CarNew(dir,sec);
        //printf("Vehicle Generated %d\n",newptr->carID);

        //Calculate Vehicle Arrival Rate
        allvehicles ++;
        //printf("Rate %.2f\n",(float) sec/allvehicles);

        SchedCross(newptr,sec);  //Schedule vehicle for crossing
        //CarPrint(newptr,sec );  //Print New vehicle created



        //*****************************************
        //      Send Light Status to Vehicle
        //*****************************************

        //printf("Arrive Queue Status | Left: %d Right & Straight: %d  \n\n",\
           Lane[0][1].count + Lane[1][3].count + Lane[2][5].count + Lane[3][7].count,\
           Lane[0][0].count + Lane[1][2].count + Lane[2][4].count + Lane[3][6].count);

        DirArray[dir].arrvNext = arrival;
        DirArray[dir].arrvNum++;
    }
    else{
        DirArray[dir].arrvNext--;
    }
}

//Code used to read parameter file
int readParameters(char* fileName) {
    FILE* fp = fopen(fileName, "r");
    if (fp) {
        char label[50];
        char value[100];

        while (fscanf(fp,"%[^:]:%s\n",label, value) == 2) {
            if (strcmp(label, "SimTime") == 0)
                timers = atoi(value);
            if (strcmp(label, "Mean") == 0)
                m = atoi(value);
            if (strcmp(label, "DynamicT2P") == 0)
                T2P = atoi(value);
            if(strcmp(label, "SpeedLowerBound") == 0)
                sp_low_bound = atoi(value);
            if(strcmp(label, "SpeedUpperBound") == 0)
                sp_upper_bound = atoi(value);
            if(strcmp(label, "ComDistance") == 0)
                com_dist = atoi(value);
            if(strcmp(label, "PercentVehiclesRight") == 0)
                perVRight = atoi(value);
            if(strcmp(label, "PercentVehiclesLeft") == 0)
                perVLeft = atoi(value);
            if(strcmp(label, "PercentVBuses") == 0)
                perBuses = atoi(value);
            if(strcmp(label, "CycleTime") == 0)
                IntTimer= atoi(value);
            if(strcmp(label, "EastWestTurn") == 0)
                ewturnper= atof(value);
            if(strcmp(label, "EastWestSR") == 0)
                ewper= atof(value);
            if(strcmp(label, "NorthSouthTurn") == 0)
                nsturnper= atof(value);
            if(strcmp(label, "NorthSouthSR") == 0)
                nsper = atof(value);
            if(strcmp(label, "OutputPath") == 0)
                strcpy(outputpath[1], value);
                strcpy(outputpath[2], value);
                strcpy(outputpath[3], value);
                strcpy(outputpath[4], value);
                strcpy(outputpath[5], value);
                strcpy(outputpath[6], value);

        }
        fclose(fp);
        return 1;
    }
    else {
        fprintf(stderr, "Parameter file not found in: %s\n\n", fileName);
        return 0;
    }
}


//******************************x**********************************
// main
//****************************************************************
int main(int argc, char *argv[]) {
    int i, j, opt,dir,sec;

    //****************************************************
    // Change this to the location of your parameter file
    //****************************************************
    if (!readParameters("/Users/alejflor/thesis/01Pretime/01-pretime-param.dat"))
    {
        fprintf(stderr, "Go to the main section of 01-pretime.c and set the parameter path file!\n");
        return 1;
    }


    //**********************************
    //          User Prompt
    //**********************************
//    printf("Simulation duration in seconds: ");
//    scanf("%d", &timers);
//    printf("Mean of vehicles arriving to the intersection as an integer: ");
//    scanf("%lf", &mean);
//    printf("Time needed for each vehicle to pass intersection in seconds: ");
//    scanf("%d", &time2pass);

    //Simulation tim ein seconds
    //timers = 1800;

    //To set variable time to pass 1=ON 0=OFF
    //T2P = 1;

    //Specify speed lower and upper bound (INT ONLY)
    //sp_low_bound =25;  //25
    //sp_upper_bound =35;

    //Specify Distance in meters when vehicle start communicating with intersection hub
    //com_dist=300;

    //Percentage of vehicle going Left and Right
    //% vehicles headed right = 100 - (right + left)
    //Headed straight 60%
    //perVRight = 20;  //Headed right
    //perVLeft = 20; //Headed Left

    //Percent of busses
    //perBuses = 20;


    //Set the mean between 2(heavy traffic) - 11(Light Traffic
    //int m = 8;  //3, 5, 7, 11, 19, 27, 35, 43
    mean0 = m;   //10= 24  //6 = 40
    mean1 = m;   //9 = 26  //5 = 48
    mean2 = m;   //8 = 28  //4 = 60
    mean3 = m;   //7 = 32  //3 = 80x


    //IntTimer = 25;  //total cycle time
    nsturn = nsturnper * IntTimer; //20 sec in rush and 13 in light
    ns = nsper * IntTimer;  //80 sec during rush and 52 in light
    ewturn = ewturnper * IntTimer; //20
    ew = ewper *  IntTimer; //80

    //100 for heavy
    //50 for light and moderate

    //**************************************************************
    //                 Change File Paths Before Running!
    //**************************************************************
    f1 = fopen(strcat(outputpath[1],"1_pretime_sim.csv"), "w");
    f2 = fopen(strcat(outputpath[2],"1_pretime_output.txt"), "w");
    f3 = fopen(strcat(outputpath[3],"1_pretime_array.csv"), "w");
    f4 = fopen(strcat(outputpath[4],"0_pretime_stats.csv"), "a");
    fl = fopen(strcat(outputpath[5],"1_pretime_Lplatoon.csv"), "w");
    fsr= fopen(strcat(outputpath[6],"1_pretime_SRplatoon.csv"), "w");
    //d2 = fopen("/Users/alejflor/thesis/Results/multi/pretime-in/0_mx-2.csv", "w");

    fprintf(f1,"CarID,From,To,Lane,ETA,Wait,SchedT,rSchedT,T2P,Type,ETD\n");
    fprintf(f2,"Stats\n");
    fprintf(f3,"TIC,0-Left,0-Straight,0-Right,1-Left,1-Straight,1-Right,2-Left,2-Straight,2-Right,3-Left,3-Straight,3-Right \n");
    fprintf(fl,"Lane,Size\n");
    fprintf(fsr,"Lane,Size\n");

    for (i=0; i<3; i++) {
        vstat[i].num=0;
        vstat[i].nums=0;
        vstat[i].numl=0;
        vstat[i].numr=0;
        vstat[i].waitsum=0;
        vstat[i].waitmax=0;
    }

    vClk = SetVClk(5,0,0); // start at 07:00:00
    srand(getpid()); //Use in production
    //srand(500);  //use for testing

    InitTime(); // real clock, starting from 0 sec0
    // taking care of commendline options
    while((opt=getopt(argc,argv,"hT:A:Q:X:")) != -1) switch(opt) {
            case 'h':
                printf("command -T simulation time in sec -A arrival rate per 10 sec -Q max queue len\n");
                break;
            case 'T': timers=atoi(optarg);
                break;
            case 'A': mean = atof(optarg);
                printf("mean arrival: mean=%02f \n", mean);
                break;
            case 'Q': MAXQLEN=atoi(optarg);
                if (MAXQLEN>200 || MAXQLEN<0) MAXQLEN = 20; //set backe to default
                printf("Max Queue lwngth: MAXQLEN=%d \n", MAXQLEN);
                break;
                //Removed no longer an option
                //case 'X': time2pass=atoi(optarg);
                //printf("Time to pass the intersaction: time2pass secs =%d \n", time2pass);
                //break;
            default:
                fprintf(stderr, "Err: no such option:`%c'\n",optopt);
        }

    for (i=0; i<4; i++) { // for East, South, West, North directions
        QueueInit(&QSR[i]); //address of QSR
        QueueInit(&QL[i]); //address of QL
        DirArray[i].dirID=i;
        DirArray[i].arrvNum = 0;
        DirArray[i].arrvNext = 0;
        DirArray[i].arrvMaxT = 0;
        DirArray[i].arrvMeanT =0;
        DirArray[i].arrvMinT = INT_MAX;
    }

    //Set the mean for each side
    DirArray[0].arrvMeanT = mean0;
    DirArray[1].arrvMeanT = mean1;
    DirArray[2].arrvMeanT = mean2;
    DirArray[3].arrvMeanT = mean3;

    //Initialize Cross
    InitCross(MAXTIC);


    // display the waiting line every 60sec (1 min)
    //Run this for every second in the hours (timer = 3600 = sec in an an hour)
    for (sec=0; sec<timers; sec++) {

        //printf("TIME: %d\n",sec);

        for (dir=0; dir<4; dir++) {
            CarArrive(dir,sec);
        }

        fprintf(f3,"%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d    \n", sec, L[0][sec],S[0][sec],R[0][sec],L[1][sec],S[1][sec],R[1][sec],L[2][sec],S[2][sec],R[2][sec],L[3][sec],S[3][sec],R[3][sec]);

        HandleCross(dir,sec);


    }

    printf("\n\n***************************************************\n");
    printf("                     PRINT STATS                    \n");
    printf("****************************************************\n");


    printf("Pretime Vehicle Algorithm \n\n");
    fprintf(f2,"Pretime Vehicle Algorithm \n\n");

    printf("Parameters\n");
    fprintf(f2,"Parameters\n");
    printf("Simulating Duration: %d \n", timers);
    fprintf(f2,"Simulating duration %d \n", timers);

    nResidue = QSR[0].len + QSR[1].len + QSR[2].len + QSR[3].len + QL[0].len + QL[1].len + QL[2].len + QL[3].len;

    double fac = timers/60.0;
    printf("Mean for East Direction: %.0lf\n",mean0);
    printf("Mean for South Direction: %.0lf\n",mean1);
    printf("Mean for West Direction: %.0lf\n",mean2);
    printf("Mean for North Direction: %.0lf\n",mean3);

    fprintf(f2,"Mean for East Direction: %.0lf\n",mean0);
    fprintf(f2,"Mean for South Direction: %.0lf\n",mean1);
    fprintf(f2,"Mean for West Direction: %.0lf\n",mean2);
    fprintf(f2,"Mean for North Direction: %.0lf\n",mean3);

    printf("Dynamic T2P: %d \n",T2P);
    printf("Speed Lower Bound: %d\n",sp_low_bound);
    printf("Speed Upper Bound: %d\n",sp_upper_bound);
    printf("Distance: %d\n",com_dist);
    printf("%% Vehicles Headed Right: %d\n",perVRight);
    printf("%% Vehicles Headed Left: %d\n",perVLeft);
    printf("%% Vehicles Headed Straight: %d\n",100-perVRight-perVLeft );
    printf("%% Sedans: %d\n",100-perBuses);
    printf("%% Buses: %d\n\n",perBuses);
    printf("Total Cycle: %.2f\n",IntTimer );
    printf("East/West Turn %.2f \n",ewturn);
    printf("East/West S/R: %.2f \n",ew);
    printf("North/South Turn: %.2f \n",nsturn);
    printf("North/Soutn S/R: %.2f \n",ns);


    fprintf(f2,"Dynamic T2P: %d \n",T2P);
    fprintf(f2,"Speed Lower Bound: %d\n",sp_low_bound);
    fprintf(f2,"Speed Upper Bound: %d\n",sp_upper_bound);
    fprintf(f2,"Distance: %d\n",com_dist);
    fprintf(f2,"%% Vehicles Headed Right: %d\n",perVRight);
    fprintf(f2,"%% Vehicles Headed Left: %d\n",perVLeft);
    fprintf(f2,"%% Vehicles Headed Straight: %d\n",100-perVRight-perVLeft );
    fprintf(f2,"%% Sedans: %d\n",100-perBuses);
    fprintf(f2,"%% Buses: %d\n\n",perBuses);
    fprintf(f2,"Total Cycle: %.2f\n",IntTimer );
    fprintf(f2,"East/West Turn %.2f \n",ewturn);
    fprintf(f2,"East/West S/R: %.2f \n",ew);
    fprintf(f2,"North/South Turn: %.2f \n",nsturn);
    fprintf(f2,"North/Soutn S/R: %.2f \n",ns);


    float arvl_rate = (float)(nArrv/fac);
    float dept_rate = (float)(nPass/fac);
    printf("Incoming Rate: %lf cars/min\n",arvl_rate);
    fprintf(f2,"Incoming Rate: %lf cars/min\n",arvl_rate);
    printf("Outgoing Rate: %lf cars/min\n",dept_rate);
    fprintf(f2,"Outgoing Rate: %lf cars/min\n",dept_rate);

    //Print count of vehicles that passed and didn't
    printf("\nArrivals:%d Passed:%d Remaining:%d Errors:%d Sum:%d\n", nArrv, nPass, nResidue,errors,nPass+nResidue);
    printf("Percent of Vehicles that Passed: %.2f \n\n",(float)nPass/nArrv*100 );

    fprintf(f2,"\nArrivals:%d Passed:%d Remaining:%d Errors:%d Sum:%d\n", nArrv, nPass, nResidue,errors,nPass+nResidue);
    fprintf(f2,"Percent of Vehicles that Passed: %.2f \n\n",(float)nPass/nArrv*100 );


    // Count Vehicler per Direction
    printf("Vehicles that passed\n");
    printf("Going Straight: %d\n",vstat[0].nums + vstat[1].nums + vstat[2].nums + vstat[3].nums);
    printf("Going Left: %d\n",vstat[0].numl + vstat[1].numl + vstat[2].numl + vstat[3].numl);
    printf("Going Right: %d\n",vstat[0].numr + vstat[1].numr + vstat[2].numr + vstat[3].numr);

    fprintf(f2,"Vehicles that passed\n");
    fprintf(f2,"Going Straight: %d\n",vstat[0].nums + vstat[1].nums + vstat[2].nums + vstat[3].nums);
    fprintf(f2,"Going Left: %d\n",vstat[0].numl + vstat[1].numl + vstat[2].numl + vstat[3].numl);
    fprintf(f2,"Going Right: %d\n",vstat[0].numr + vstat[1].numr + vstat[2].numr + vstat[3].numr);

    int PLeft = vstat[0].numl + vstat[1].numl + vstat[2].numl + vstat[3].numl;
    int PSR = vstat[0].nums + vstat[1].nums + vstat[2].nums + vstat[3].nums + vstat[0].numr + vstat[1].numr + vstat[2].numr + vstat[3].numr;


    // Count Vehicles per direction
    char roadstr[4][15] = {"\nEast ","South","West ","North"};
    for (i=0; i<4; i++)
        if (road[i].num>0) {
            float wavg = road[i].waitsum / (float)road[i].num;
            printf("%s Num:%d  WT: %d  Max WT:%.0f  Avg WT:%.2f\n", roadstr[i], road[i].num,road[i].waitsum, road[i].waitmax, wavg );
            fprintf(f2,"%s Num:%d  WT: %D  Max WT:%.0f  Avg WT:%.2f\n", roadstr[i], road[i].num,road[i].waitsum, road[i].waitmax, wavg );
        }


    printf("\nSum Wait Time: %d\n", wait_sum);
    printf("Average Wait Time: %.2f\n",(float)wait_sum/nPass);

    fprintf(f2,"\nSum Wait Time: %d\n", wait_sum);
    fprintf(f2,"Average Wait Time: %.2f\n",(float)wait_sum/nPass);

    printf("\nNumber of Busses: %d\n",count_busses);
    printf("Number of Cars: %d\n",count_vehicles);
    fprintf(f2,"\nNumber of Busses: %d\n",count_busses);
    fprintf(f2,"Number of Cars: %d\n",count_vehicles);

    printf("\nLongest Wait Time: %.0f\n",maxwt);
    printf("VStop: %d VPass: %d\n",vstop,nPass);
    printf("Percent of Vehicles that Stopping: %.2f\n\n",(float)vstop/nPass*100);

    fprintf(f2,"\nLongest Wait Time: %.0f \n",maxwt);
    fprintf(f2,"VStop: %d VPassed: %d\n",vstop,nPass);
    fprintf(f2,"Percent of Vehicles that Stopping: %.2f\n\n",(float)vstop/nPass*100);


    printf("******************************  Platoon Information  *******************************\n");
    char dirr[8][15] = {"East SR ","East L  ","South SR","South L ","West SR ","West L  ","North SR","North L "};
    for (i=0; i<8; i++){
        printf("%s- Platoons:%d  Vehicle:%d   Avg Size:%.2f   Max:%d  AvgTime:%.2f   MaxTime:%d \n",dirr[i],placount[i],platotal[i],(double)platotal[i]/placount[i], plamax[i], (double)plaTimesum[i]/placount[i] ,plaTmax[i] );
        fprintf(f2,"%s- Platoons:%d  Vehicle:%d   Avg Size:%.2f   Max:%d  AvgTime:%.2f   MaxTime:%d \n",dirr[i],placount[i],platotal[i],(double)platotal[i]/placount[i], plamax[i], (double)plaTimesum[i]/placount[i],plaTmax[i] );
    }
    //Average Time = # of platoons/total time taken by all platoons


    //            Mean,AWT, Arriv,Pass,Remain,%pass,%stop,MaxWT, LE,SRE,LS,SRS,LW,SRW,LN,SRN,LWT
    fprintf(f4,"%.2f,%.2f,%d,%d,%d,%.2f,%.2f,%.2f",
            mean0,
            (float)wait_sum/nPass,
            nArrv,
            nPass,
            nResidue,
            (float)nPass/nArrv*100,
            (float)vstop/nPass*100,//0,0,0,0,0,0,0,0,maxwt);
            maxwt);

    for (i=0; i<8; i++){
        fprintf(f4,",%d,%d,%.2f,%d,%.2f,%d",placount[i],platotal[i],(double)platotal[i]/placount[i], plamax[i], (double)laneTotal[i]/plaTimesum[i] ,plaTmax[i] );
    }
    fprintf(f4,"\n");


    fclose(d2);
    fclose(f4);
    fclose(f3);
    fclose(f1);
    fclose(f2);
    return 0;
}
