
/* Author: Alejandro Flores
 * Dashboard Traffic Light System
 * UNM ECE Thesis
 * Spring 2016
 * Modified: 4/18/2016
 *
 * Summary:  This program can be used to simmulate the FIFO and Laxy Algorithm
 * for a 4-way traffic intersection
 *
 * Order in which functions are called
 * InitTime()
 * CarArrive()
 *    Car New()
 *    IdentifyLane ()
 *    Enqueue()
 *    ScheduleCross()
 * ScheduleCross()
 *    setL2Red()
 *    setS2Red()
 *    setSR2Red()
 *    T2TP()
 *    Carprint()
 * HandleCross ()
 *    QueueTop()
 *    Dequeue()
 *    CarPass()
 * CarPass()
 *    Conflict()
 *
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
//Used to determin when the next vehicle arrives not when the actual vehicle arrives
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
typedef struct {int carID, schedT,arrivT,deptT, from, to,lane, turn, speed, type, t2p,entime,extime,deltat,firstv,lastv; float dist,eta,etd,wait;} DTVehicle;
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
char outputpath[11][100];
int m;


//Parameters used to import file
DTVehicle *Pvehicle[4][9999];
int columns = 6;
char *path0 = 0;
char *path1 = 0;
char *path2 = 0;
char *path3 = 0;
int Count0 = 0,Count1 = 0,Count2 = 0, Count3= 0;

//Variable used to determin platoons
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

//Variables used to collect stats
int wtd[4];   //Wait per direction
float maxwt = 0;  //max wait time
int vstop = 0;  //Count Vehicles that had to stop
int errors = 0;
int count_vehicles = 0;
int count_busses = 0;
int wait_sum= 0;
int  nDetour=0, nPass=0, nArrv=0, nResidue=0;
int allvehicles = 0;
int trigger;
int ON;


//Variable used for lazy scheduling
int ecount = 0;
int eflush = 0;
int scount = 0;
int sflush = 0;
int wcount = 0;
int wflush = 0;
int ncount = 0;
int nflush = 0;
int lcount[4];
DTVehicle *espot[500];
DTVehicle *sspot[500];
DTVehicle *wspot[500];
DTVehicle *nspot[500];

int vQ, EWT,NST ,nsTcount, ewTcount ;
DTVehicle *ewspot[500];
DTVehicle *nsspot[500];
int enable;
int T2P;
int perVRight;
int perVLeft;
int perBuses;


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
            lcount[i] = 0;
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

//Function used to count how many line in the file being imported
int Lines(char * buffer) {
    int lines = 0 ;
    char * pcomma;
    pcomma=strchr(buffer,',');
    while (pcomma!=NULL) {
        lines++;
        pcomma=strchr(pcomma+1,',');
    }
    return lines/(columns-1);
}

//Function used to identify how many commas in the file being imported
int Commas(char * buffer) {
    int commas = 0;
    char * pcomma;
    //Code to identify how many line and commas we have in the file
    pcomma=strchr(buffer,',');
    while (pcomma!=NULL) {
        commas++;
        pcomma=strchr(pcomma+1,',');
    }
    return commas;
}

//Function that will open the file and save it to buffer
char *openfile  (char * file){
    char *buffer = 0;
    long length;
    char * pcomma;

    FILE *f = fopen(file, "rb");

    if (f) {
        fseek(f, 0, SEEK_END);
        length = ftell(f);  // find file size
        fseek(f, 0, SEEK_SET);
        buffer = malloc(length);
        if (buffer) {
            fread(buffer, 1, length, f);
        }
        fclose(f);
    }
    return buffer;
}

//This function help identify what lane the vehicle is arriving from
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

    //Determine the Platoon Mx Size
    for (i=0; i<8; i++){
        if (plasum[i] > plamax[i]){
            plamax[i] = plasum[i];
        }
        //Determine Platoon Max Time
        if (plaTimetotal[i] > plaTmax[i]){
            plaTmax[i] = plaTimetotal[i];
        }
    }

    //If vehicle is headed left, cut all othe rplatoons
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

//Function where most of the vehicle parapeters are determined such as
//speed,from,to,ID, lane, and others
DTVehicle *CarNew(int d, int k) {
    DTVehicle *newptr;
    int e,mph,lane,vl;
    double msec = 0;
    float arrivT;

    // car waiting in QSR, 70% go straight, 15% left/right turn, respectively
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
    //printf("MPH Before: %d\n",mph);

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

    //printf("Speed: %f\n", speed);
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

//Read the delimited file and save the items into
DTVehicle * import(char * file, int dir) {
    char *buffer = 0;
    int LN, CM;
    int z = 0;
    int i = 0;
    int lane;
    double msec;
    DTVehicle *CarPtr;
    char *pcomma;
    char *cp;
    int g =0;
    int n,vr,buses;

    for (n=0; n<1000; n++) {
        Pvehicle[dir][n] = 0;
    }

    //Open File
    buffer = openfile(file);
    //printf("%s\n",buffer);

    //Identify Line and Comma count of buffer
    LN = Lines(buffer);
    CM = Commas(buffer);
    printf("Lines: %d Commas: %d\n\n", LN, CM);

    //Do this per line until the last line where z is the number of lines
    cp = buffer;
    while (z < LN) {
        CarPtr = (DTVehicle *) malloc(sizeof(DTVehicle));

        //Vehicle ID Specified by the Scheduler
        pcomma = strchr(cp, ',');
        *pcomma = 0; //string terminater
        CarPtr->carID = atof(cp);

        cp = pcomma + 1;
        pcomma = strchr(cp, ',');
        *pcomma = 0; //string terminater
        CarPtr->arrivT = atoi(cp);

        //Direction specified by
        cp = pcomma + 1;
        pcomma = strchr(cp, ',');
        *pcomma = 0; //string terminater
        //CarPtr->from = atof(cp);
        CarPtr->from = dir;

        cp = pcomma + 1;
        pcomma = strchr(cp, ',');
        *pcomma = 0; //string terminater
        CarPtr->speed = atoi(cp);

        cp = pcomma + 1;
        pcomma = strchr(cp, ',');
        *pcomma = 0; //string terminater
        CarPtr->dist = atoi(cp);

        cp = pcomma + 1;
        CarPtr->type = atoi(cp); //Function will stop at a newline


        //*************************
        // Assign other parameters
        CarPtr->to=Straight; // 60% Go Straight
        if ((g=rand()%100)<perVLeft) {
            CarPtr->to = Left; // 20% turn left
        }
        vr= 100-perVRight;
        if (g>=vr) {
            CarPtr->to = Right;// 20% turn right
        }


        //Match MPH of last vehicle if lane is not empty
        if (Lane[dir][lane].count > 0 && CarPtr->speed > Lane[dir][lane].speed) {
            CarPtr->speed = Lane[dir][lane].speed;
        }

        lane = IdentifyLane(dir,CarPtr->to);
        CarPtr->lane = lane;

        CarPtr->deptT = 0;

        msec = (CarPtr->speed * .44704);  //convert mph to meters/sec
        CarPtr->arrivT = round(com_dist/msec);

        CarPtr->schedT =0;
        CarPtr->etd =0;
        //CarPtr->carID = ++gID;
        //printf("VID!!!! %d",CarPtr->carID);

        Pvehicle[dir][z] = CarPtr; //Possible problem
        //tprintf("Adding Car to %d List Vehicle: %d",dir,CarPtr->carID);

        z++;
        cp = pcomma + 2;

    }
    return 0;
}

DTVehicle * NewVehicle(int dir, int k) {
    DTVehicle *newptr;

    if (dir==0){
        newptr = Pvehicle[0][Count0];
        Count0++;
    }
    else if (dir==1){
        newptr = Pvehicle[1][Count1];
        Count1++;
    }
    else if (dir==2){
        newptr = Pvehicle[2][Count2];
        Count2++;
    }

    else if (dir==3){
        newptr = Pvehicle[3][Count3];
        Count3++;
    }

    nArrv++; // total number arrival of cars


    newptr->eta = k + newptr->arrivT;
    //newptr->carID = ++gID;
    //printf("B\n");
    if (newptr->to==Left) {
        //tprintf("\nAdding Car to QL Vehicle: %d From: %d \n",newptr->carID,dir);
        Enqueue(&QL[dir], newptr); // going to left turn lane
        Lane[dir][newptr->lane].count += 1;  //Increase the count on vehicles in the lane
        Lane[dir][newptr->lane].speed = newptr->speed;  //This is in mph
        //printf("LTQ TOP: %d\n",QueueTop(&QL[dir])->carID);
    }
    else {
        //tprintf("\nAdding Car to QSR Vehicle: %d From: %d \n",newptr->carID,dir);
        Enqueue(&QSR[dir], newptr); // going to the right lane
        Lane[dir][newptr->lane].count += 1;
        Lane[dir][newptr->lane].speed = newptr->speed;  //This is in mph
        //printf("SRQ TOP %d\n",QueueTop(&QSR[dir])->carID);
    }

    return (newptr);

}


//Used to print the vehicles that are being created
void CarPrint(DTVehicle *cptr,int clk) {
    printf("*******************************************************************************************************************************************************\n");
    printf("%d:vID Type:%c T2P: %d From:%c Going:%c Lane:%d Speed:%d mph Distance:%.2f meters Tic:%d ArrvT: %d ETA:%.0f sec SchedT: %d  ETD:%.0f  Waiting: %.0lf \n",
           cptr->carID,strType[cptr->type], cptr->t2p, strDir[cptr->from], strTurn[cptr->to],cptr->lane, cptr->speed, cptr->dist,clk,cptr->arrivT, cptr->eta,cptr->schedT, cptr->etd,cptr->wait);
    printf("********************************************************************************************************************************************************\n\n");
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
        time2pass = 2;
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

    if (enable == 0){
        delay = 0;
    }

    //PROCESS vehicles turning left
    if (to == Left) {

        //Add car to the back
        if (ETA > L_last_tslot[from]) {  //If vehicle arrival time is after last vehicle
            x = ETA;
        }
        else {
            x = 1 + L_last_tslot[from];  //If not, then time slot is after last vehicle
        }
    }

        //PROCESS vehicles turning right
    else if (to == Right) {
        if (ETA + delay  > R_last_tslot[from]) {
            x = ETA + delay;
        }
        else {
            if (from == 2) {
                x = R_last_tslot[from] ;
            }
            else{
                x = 1 + R_last_tslot[from];
            }
        }
    }

        //   PROCESS vehicles going straight
    else {
        if (ETA + delay > S_last_tslot[from]) {
            x = ETA + delay;
        }
        else {
            if (from == 2) {
                x = S_last_tslot[from] ;
            }
            else{
                x = 1 + S_last_tslot[from] ;
            }
        }
    }

    pCar->schedT = x;  //This record the time the vehicle actually crossed


    //Set T2P for when lazy is off
    if (enable == 0 ){
        time2pass = t2p(pCar->schedT, pCar->type, pCar->to, ETA);
        pCar->t2p = time2pass;
    }

    //******************************************
    //                Lazy T2P
    //******************************************

    //T2P for First vehicle in the staright direction
    if (enable == 1 & pCar->firstv == 1){
        time2pass = t2p(pCar->schedT, pCar->type, pCar->to, ETA);
        pCar->t2p = time2pass;
    }

    //T2P for the vehicle headed left
    if (enable == 1 & pCar->to == Left){
        if (lcount[from] == 0){
            time2pass = t2p(pCar->schedT, pCar->type, pCar->to, ETA);
            pCar->t2p = time2pass;
        }
        if (lcount[from] >= 1){
            if (pCar->type == 0){
                time2pass = 1;
                pCar->t2p = time2pass;
            }
            if (pCar->type == 1){
                time2pass = 2;
                pCar->t2p = time2pass;
            }
        }
        lcount[from]++;
    }


    if (enable == 1 & pCar->to != Left){
       time2pass = pCar->t2p ;
    }


    //******************************************
    //Calculate waiting time for each vehicle
    //******************************************

    if (enable == 0) {
        pCar->extime = 0;
        pCar->entime = 0;
        pCar->wait = pCar->schedT - pCar->eta;
    }

    if (enable == 1) {
        pCar->deltat = delay;
        pCar->wait = (pCar->schedT - pCar->eta);// + delay);
    }



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
        for (i = 0; i < time2pass; i++) {
            //Now block the time slot in the other arrays
            setS2Red((from + 1) % 4, x + i);  //printf("Block SR: %d\n",((from + 1) % 8));
            setL2Red((from + 1) % 4, x + i);   //printf("Block L: %d\n",((from + 1) % 8));
            setS2Red((from + 2) % 4, x + i);  //printf("Block SR: %d\n",((from + 2) % 8));
            setL2Red((from + 3) % 4, x + i);   //printf("Block L: %d\n",((from + 3) % 8));
        }
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

        for (i = 0; i < time2pass; i++) {
            setS2Red((from + 1) % 4, x + i); //printf("Block S: %d\n",((from + 1) % 4));
        }

        if (R_last_tslot[from] < (x + time2pass)) R_last_tslot[from] = x + time2pass;
        if (R_first_tslot[from] < (x + time2pass)) R_first_tslot[from] = x + time2pass;
        if (S_last_tslot[from] < (x + time2pass)) S_last_tslot[from] = x + time2pass;
        if (S_first_tslot[from] < (x + time2pass)) S_first_tslot[from] = x + time2pass;
    }

    else {
        //printf("T2P: %d \n",time2pass);
        for (i = 0; i < time2pass; i++) {
            if (S[from][x + i] == EMPTY) { S[from][x + i] = id;}
            if (R[from][x + i] == EMPTY) { R[from][x + i] = VOID; }
        }

        for (i = 0; i < time2pass; i++) {
            //Now block the time slot in the other arrays
            //printf("Blocking Dir:%d  Slot: %d\n",(from + 1) % 4, x+i);
            setS2Red((from + 1) % 4, x + i);   //printf("Block S: %d\n",((from + 1) % 4));
            setL2Red((from + 2) % 4, x + i);   //printf("Block L: %d\n",((from + 2) % 4));
            setSR2Red((from + 3) % 4, x + i);   //printf("Block SR: %d\n",((from + 3) % 4));
            setL2Red((from + 3) % 4, x + i);   //printf("Block L: %d\n",((from + 3) % 4));
        }
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
    wait_sum += w;

    //calculate longest wait time
    if (w > maxwt){
        maxwt = w;
    }

    //Sum the total vehicles that had to wait in all directions
    if (w>1) {
        vstop++;
    }

    //Print a list of vehicles that passed into the sim file
    fprintf(f1,"%d,%c,%c,%d,%.2f,%.02f,%d,%d,%c,%.2f\n",carptr->carID,strDir[carptr->from],strTurn[carptr->to],carptr->lane,carptr->eta,w,carptr->schedT,carptr->t2p,strType[carptr->type],carptr->etd);

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
    int id;
    int ids, idr, i;
    int t2p = 0;
    DTVehicle *carptr;

    //Process Vehicles Going Left 
    id = L[dir][clk];
    if (id > 0) { // Left left-turn car go
        if ((carptr = QueueTop(&QL[dir])) != NULL) {

            if (id != carptr->carID) {
                printf("\nERROR L Tic:%d From:%c Array VID:%d Queue VID:%d \n\n", clk, strDir[dir], id,
                       carptr->carID);
                errors += 1;
            }
            tprintf("Calling Dequeue QL From: %d \n", dir);
            carptr = Dequeue(&QL[dir]); //Get pointer
            CarPass(carptr,clk);

            printf("****************  Passing  *********************\n");
            printf("      GO LEFT | VID:%d Tic:%d From:%c  \n", id, clk, strDir[dir]);
            printf("************************************************\n");

            //Clear reservation
            t2p = carptr->t2p;
            for (i = 0; i < t2p; i++) {
                if (L[dir][clk + i] == id) L[dir][clk + i] = PASSED;
            }

        }
    }

    // Process Vehicles Going Straight or Turning Right 
    idr = R[dir][clk];
    ids = S[dir][clk];

    if (idr > 0 || ids > 0) { //Check to see if Right and Straight arrays are not empty

        if ((carptr = QueueTop(&QSR[dir])) != NULL) {  //Check Queue SR is not empty

            tprintf("Calling Dequeue QSR From: %d\n", dir);
            carptr = Dequeue(&QSR[dir]);
            CarPass(carptr,clk);

            if (R[dir][clk] > 0) {
                if (R[dir][clk] != carptr->carID) {
                    printf("\nERROR R Tic:%d From:%c Array VID:%d Queue VID:%d \n\n", clk, strDir[dir], idr,
                           carptr->carID);
                    errors += 1;
                }
                printf("****************  Passing  *********************\n");
                printf("        GO RIGHT | VID:%d Tic:%d From:%c  \n", idr, clk, strDir[dir]);
                printf("************************************************\n");

                //Clear reservation
                t2p = carptr->t2p;
                for (i = 0; i < t2p; i++) {
                    if (R[dir][clk + i] == idr) R[dir][clk + i] = PASSED;

                }
            }

            if (S[dir][clk] > 0) {

                if (S[dir][clk] != carptr->carID) {
                    printf("\nERROR S Tic:%d From:%c ArrayID:%d QueueID:%d \n\n", clk, strDir[dir], ids,
                           carptr->carID);
                    errors += 1;
                }
                printf("****************  Passing  *********************\n");
                printf("         GO STRAIGHT | VID:%d Tic:%d From:%c \n", ids, clk, strDir[dir]);
                printf("************************************************\n");

                //Clear reservation
                t2p = carptr->t2p;
                for (i = 0; i < t2p ; i++) {
                    S[dir][clk + i] = PASSED;
                }

            }
        }
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

        //Determin when the next vehicle arrives
        arrival = RandPoisson(DirArray[dir].arrvMeanT);


        //Determin the Max arrival time
        if (arrival > DirArray[dir].arrvMaxT) {
            DirArray[dir].arrvMaxT = arrival;
        }
        if (arrival < DirArray[dir].arrvMinT) {
            DirArray[dir].arrvMinT = arrival;
        }

        //Create new vehicle
        //newptr = CarNew(dir,sec);
        //Create new vehicle
        newptr = NewVehicle(dir, sec);

        //Count how many vehicles get created
        allvehicles ++;


        //Code used in Lazy Algorithm to determine when the
        //Lazy algorithm Should start operating
        if ( ON == 1) {
            if (trigger > sec) {
                enable = 0;

            }
            if (trigger <= sec) {
                enable = 1;
            }
        }

        //Regardless if Lazy Algorithm is enabled or not
        //Process vehicles going left as normal
        if (newptr->to == Left){
            SchedCross(newptr,sec);  //Schedule vehicle for crossing
        }


        // This is part of the code only applies to the Lazy Algorithm
        // Checks to see if the vehicle is going straight or right
        if (enable == 1 & newptr->to != Left){
            if (newptr->from == East ){
                ecount ++;  // Count the numnber of vehicles to hold until release
                espot[ecount] = newptr;
                espot[ecount]->entime = sec;  // Time when vehicle gets created
                //If the vehicle count has met the quorum then release the vehicles to be processed
                if (ecount == vQ){
                    eflush = 1;  //Trigger Processing
                    espot[ecount]->lastv = 1;
                }
            }

            if (newptr->from == West){
                wcount ++;
                wspot[wcount] = newptr;
                wspot[wcount]->entime = sec;
                if (wcount == vQ){
                    wflush = 1;  //Trigger Processing
                    wspot[wcount]->lastv = 1;
                }
            }

            if (newptr->from == North ){
                ncount ++;
                nspot[ncount] = newptr;
                nspot[ncount]->entime = sec;
                if (ncount == vQ ){
                    nflush = 1;  //Trigger Processing
                    nspot[ncount]->lastv = 1;
                }
            }

            if (newptr->from == South){
                scount ++;
                sspot[scount] = newptr;
                sspot[scount]->entime = sec;
                if (scount == vQ ){
                    sflush = 1;  //Trigger Processing
                    sspot[scount]->lastv = 1;
                }
            }

        }


        //***************************************************************
        //                            Dispatch
        //***************************************************************
        //This is the part of the code that processes the vehicles for EW
        //Check to see if the Vehicle Quorum count is met or if a specified time delay has passed
        if ((enable == 1) & (eflush == 1 | sec >= ewTcount)) {
            if (ecount > 0) {
                int c = 1;
                while (c <= ecount) {
                    espot[c]->extime = sec;    //Used to determine waiting time
                    espot[c]->deltat = 0;
                    //Add the time the veicle was waiting to the over vehicle waiting time
                    espot[c]->deltat = espot[c]->extime - espot[c]->entime;
                    if (c == 1){
                        espot[c]->firstv = 1;
                    }

                    // Code used to assign a 1 sec T2P to vehicle that are part of a platoon
                    if (c >1){
                        if (espot[c]->type == 0){
                            espot[c]->t2p = 1;
                        }
                        else{
                            espot[c]->t2p = 2;
                        }
                    }
                    SchedCross(espot[c], sec); //Schedule vehicle for crossing
                    c++;
                }
                //Reset Counters
                ecount = 0;
                eflush = 0;
                int z =0;
                for (z=0;z<4;z++){
                    lcount[z] = 0;
                }
            }
        }

        if ((enable == 1) & (wflush == 1 | sec >= ewTcount)) {
            if (wcount > 0) {
                int cw = 1;
                while (cw <= wcount) {
                    wspot[cw]->extime = sec;    //Used to determine waiting time'
                    wspot[cw]->deltat = 0;
                    wspot[cw]->deltat = wspot[cw]->extime - wspot[cw]->entime;
                    if (cw == 1){
                        wspot[cw]->firstv = 1;
                    }
                    if (cw >1){
                        if (wspot[cw]->type == 0){
                            wspot[cw]->t2p = 1;
                        }
                        else{
                            wspot[cw]->t2p = 2;
                        }
                    }
                    SchedCross(wspot[cw], sec); //Schedule vehicle for crossing
                    cw++;
                }
                wcount = 0;
                wflush = 0;
                int y = 0;
                for (y=0;y<4;y++){
                    lcount[y] = 0;
                }
            }
        }


        //This is the part of the code that processes the vehicles for NS
        if ((enable == 1) & (nflush == 1 | sec >= nsTcount)) {
            if (ncount > 0) {
                int n = 1;
                while (n <= ncount) {
                    nspot[n]->extime = sec;    //Used to determine waiting time
                    nspot[n]->deltat = 0;
                    nspot[n]->deltat = nspot[n]->extime - nspot[n]->entime;
                    if (n == 1) {
                        nspot[n]->firstv = 1;
                    }
                    if (n > 1) {
                        if (nspot[n]->type == 0){
                            nspot[n]->t2p = 1;
                        }
                        else{
                            nspot[n]->t2p = 2;
                        }
                    }
                    SchedCross(nspot[n], sec); //Schedule vehicle for crossing
                    n++;
                }
                ncount = 0;
                nflush = 0;
                int l=0;
                for (l=0;l<4;l++){
                    lcount[l] = 0;
                }
            }
        }
        //This is the part of the code that processes the vehicles for NS
        if ((enable == 1) & (sflush == 1 | sec >= nsTcount)){
            if (scount > 0) {
                int ns = 1;
                while (ns <= scount) {
                    sspot[ns]->extime = sec;    //Used to determine waiting time
                    sspot[ns]->deltat = 0;
                    sspot[ns]->deltat = sspot[ns]->extime - sspot[ns]->entime;
                    if (ns == 1){
                        sspot[ns]->firstv = 1;
                    }
                    if (ns >1){
                        if (sspot[ns]->type == 0){
                            sspot[ns]->t2p = 1;
                        }
                        else{
                            sspot[ns]->t2p = 2;
                        };
                    }
                    SchedCross(sspot[ns], sec); //Schedule vehicle for crossing
                    ns++;
                }
                scount = 0;
                sflush = 0;
                int u = 0;
                for (u=0;u<4;u++){
                    lcount[u] = 0;
                }
            }

        }


        //Used to determin when the configured time delay has passed
        if (enable ==1 & sec >= ewTcount ){
            ewTcount = ewTcount + EWT;
        }
        if (enable ==1 & sec >= nsTcount){
            nsTcount = nsTcount + NST;
        }


        //If lazy scheduling is disabled, just process the vehicles as they come in
        if (enable ==0 & newptr->to != Left){
            SchedCross(newptr,sec);  //Schedule vehicle for crossing
            //CarPrint(newptr,sec );  //Print New vehicle created
        }

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
            if(strcmp(label, "LazyOn") == 0)
                enable = atoi(value);
            if(strcmp(label, "LazyTrigger") == 0)
                trigger = atoi(value);
            if(strcmp(label, "LazyVQueue") == 0)
                vQ = atoi(value);
            if(strcmp(label, "LazyTDelay") == 0)
                EWT = NST = atoi(value);

            if(strcmp(label, "Path") == 0)
                strcpy(outputpath[1], value);
                strcpy(outputpath[2], value);
                strcpy(outputpath[3], value);
                strcpy(outputpath[4], value);
                strcpy(outputpath[5], value);
                strcpy(outputpath[6], value);
                strcpy(outputpath[7], value);
                strcpy(outputpath[8], value);
                strcpy(outputpath[9], value);
                strcpy(outputpath[10], value);

        }
        fclose(fp);
        return 1;
    }
    else {
        fprintf(stderr, "Parameter file not found in: %s\n\n", fileName);
        return 0;
    }
}


//**********  MAIN ****************
int main(int argc, char *argv[]) {
    int i, j, opt,dir,sec;

    //****************************************************
    // Change this to the location of your parameter file
    //****************************************************
    if (!readParameters("/Users/alejflor/thesis/03Multi/03-multi-param.dat"))
    {
        fprintf(stderr, "Go to the main section of 03-multi-param.c and set the parameter path file!\n");
        return 1;
    }


    //**********************************
    //          User Prompt
    //**********************************
    //printf("Simulation duration in seconds: ");
    //scanf("%d", &timers);
    //printf("Mean of vehicles arriving to the intersection as an integer: ");
    //scanf("%lf", &mean);
    //printf("Time needed for each vehicle to pass intersection in seconds: ");
    //scanf("%d", &time2pass);

    //Simulation tim ein seconds
    //timers = 1800;

    //Turn Lazy Algorithm ON 1=ON 0=OFF
    //enable = ON = 0;
    //trigger = 30;

    //Vehicle Queue Count
    //vQ = 30;

    //Time Delay
    //EWT = NST = 30;
    ewTcount = EWT;
    nsTcount = NST;

    //To set variable time to pass 1=ON 0=OFF
    //T2P = 1;

    //Specify speed lower and upper bound (INT ONLY)
    //sp_low_bound =25;
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
    mean3 = m;   //7 = 32  //3 = 80

    //**************************************************************
    //                  Change File Paths Before Running!
    //These directories determine where the output should be stored
    //**************************************************************/


    //This is where the simulation files are loaded
    import(strcat(outputpath[7],"multi_lane-0.csv"),0);
    import(strcat(outputpath[8],"multi_lane-1.csv"),1);
    import(strcat(outputpath[9],"multi_lane-2.csv"),2);
    import(strcat(outputpath[10],"multi_lane-3.csv"),3);

    //These are the files where the output is directed
    f1 = fopen(strcat(outputpath[1],"1_fifolazy_sim.csv"), "w");
    f2 = fopen(strcat(outputpath[2],"1_fifolazy_output.txt"), "w");
    f3 = fopen(strcat(outputpath[3],"1_fifolazy_array.csv"), "w");
    f4 = fopen(strcat(outputpath[4],"0_fifolazy_stats.csv"), "a");
    fl = fopen(strcat(outputpath[5],"1_fifolazy_Lplatoon.csv"), "w");
    fsr= fopen(strcat(outputpath[6],"1_fifolazy_SRplatoon.csv"), "w");

    fprintf(f1,"CarID,From,To,Lane,ETA,Wait,SchedT,T2P,Type,ETD\n");
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
    //srand(400);  //use for testing

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

        for (dir=0; dir<4; dir++) {
            HandleCross(dir,sec);
        }

    }

    printf("\n\n***************************************************\n");
    printf("                     PRINT STATS                    \n");
    printf("****************************************************\n");

    if (enable == 1){
        printf("Lazy Algorithm ON \n");
        fprintf(f2,"Lazy Algorithm\n");
        printf("Vehicle Queue: %d\n",vQ);
        fprintf(f2,"Vehicle Queue: %d\n",vQ);
        printf("Time Delay: %d\n\n",EWT);
        fprintf(f2,"Time Delay: %d\n\n",EWT);

    }
    else{
        printf("Single Vehicle Algorithm \n\n");
        fprintf(f2,"Single Vehicle Algorithm \n\n");
    }


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

    fprintf(f2,"Dynamic T2P: %d \n",T2P);
    fprintf(f2,"Speed Lower Bound: %d\n",sp_low_bound);
    fprintf(f2,"Speed Upper Bound: %d\n",sp_upper_bound);
    fprintf(f2,"Distance: %d\n",com_dist);
    fprintf(f2,"%% Vehicles Headed Right: %d\n",perVRight);
    fprintf(f2,"%% Vehicles Headed Left: %d\n",perVLeft);
    fprintf(f2,"%% Vehicles Headed Straight: %d\n",100-perVRight-perVLeft );
    fprintf(f2,"%% Sedans: %d\n",100-perBuses);
    fprintf(f2,"%% Buses: %d\n\n",perBuses);

    if (ON ==1){
        printf("---Lazy Algorithm Parameters---\n");
        printf("Initial Delay: %d\n",trigger);
        printf("Vehicle Queue Size: %d\n",vQ);
        printf("East  West  Time: %d \n",EWT);
        printf("North South Time: %d \n",NST);

        fprintf(f2,"---Lazy Algorithm Parameters---\n");
        fprintf(f2,"Initial Delay: %d\n",trigger);
        fprintf(f2,"Vehicle Queue Size: %d\n",vQ);
        fprintf(f2,"East  West  Time: %d \n",EWT);
        fprintf(f2,"North South Time: %d \n",NST);

    }


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
            fprintf(f2,"%s Num:%d  WT: %d  Max WT:%.0f  Avg WT:%.2f\n", roadstr[i], road[i].num,road[i].waitsum, road[i].waitmax, wavg );
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
    fprintf(f4," \n");

    fclose(d3);
    fclose(d2);
    fclose(d1);
    fclose(d0);
    fclose(f4);
    fclose(f3);
    fclose(f2);
    fclose(f1);
    return 0;
}
