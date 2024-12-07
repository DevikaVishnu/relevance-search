#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>

#define MAX_CHAR 256
#define ALLDOCS_SIZE 2000000
#define MAX_SEARCH_SUBSTRING_SIZE 10000

double time_elapsed(struct timespec *start, struct timespec *end);

//Node definition
typedef struct SuffixTreeNode {
	struct SuffixTreeNode *children[MAX_CHAR];
	struct SuffixTreeNode *suffixLink;
	int start;
	int *end;
	int suffixIndex;
	int docno;
} Node;

typedef struct relevance_count{
	int docno;
	int title_count;
	int text_count;
	int title_count_full;
	int text_count_full;
	int score;
} relevance_count;

int *relevance_score;
int *comma_index;
unsigned char **text;
Node *root = NULL;
int NUM_DOCS = 1;
int NUM_TERMINATORS;
Node *lastNewNode = NULL;
Node *activeNode = NULL;
int **indice;
int *count;
int activeEdge = -1;
int activeLength = 0;
int remainingSuffixCount = 0;
int *leafEnds;
int *rootEnd = NULL;
int *splitEnd = NULL;
int size = -1;
relevance_count *check = NULL;

//Function to initalize a new node
Node *newNode(int start, int *end, int docno) {
	Node *node =(Node*) malloc(sizeof(Node));
	int i;
	for (i = 0; i < MAX_CHAR; i++)
		node->children[i] = NULL; 

	node->start = start; 
	node->end = end;
	node->suffixIndex = -1; 
	node->docno = docno;
	node->suffixLink = root; 
	return node; 
}

void swap(struct relevance_count *a,  struct relevance_count *b) { 
    struct relevance_count t = *a; 
    *a = *b; 
    *b = t; 
}

int partition (int low,int high) { 
   	int pivot = check[high].score;    
    int i = (low - 1);  
  
    for ( int j = low; j <= high- 1; j++) {
       
        if (check[j].score >= pivot) {
            i++;
            swap(&check[i], &check[j]); 
        }
    }
    swap(&check[i + 1], &check[high]); 
    return (i + 1); 
}

void quickSort(int low, int high) { 
    if (low < high) { 
        int pi = partition( low, high); 
        quickSort( low, pi - 1); 
        quickSort( pi + 1, high); 
    } 
}

//Function to find the edge length of a node
int edgeLength(Node *n) { 
	if(n == root) //useful while searching from root
		return 0;
	return *(n->end) - (n->start) + 1; 
} 

//Function to perform walkDown of Ukkonen's method while 
// constructing the tree
int walkDown(Node *currNode) {
	if (activeLength >= edgeLength(currNode)) {
		activeEdge += edgeLength(currNode); 
		activeLength -= edgeLength(currNode); 
		activeNode = currNode; 
		return 1; 
	} 
	return 0; 
} 

//Function to perform one phase of the method for a particular document
void extendSuffixTree(unsigned char **text,int pos, int docno) {
	leafEnds[docno] = pos;
	remainingSuffixCount++;
	lastNewNode = NULL; 

	while(remainingSuffixCount > 0) {

		if (activeLength == 0) 
			activeEdge = pos; 

		if (activeNode->children[text[docno][activeEdge]] == NULL) {
			
			activeNode->children[text[docno][activeEdge]] = 
									newNode(pos, &leafEnds[docno], docno);
			if (lastNewNode != NULL) {
				lastNewNode->suffixLink = activeNode; 
				lastNewNode = NULL; 
			} 
		} else {
			Node *next = activeNode->children[text[docno][activeEdge]]; 
			
			if (walkDown(next))
				continue; 

			if (text[next->docno][next->start + activeLength] == text[docno][pos]) {
				
				if(lastNewNode != NULL && activeNode != root) {
					lastNewNode->suffixLink = activeNode; 
					lastNewNode = NULL; 
				} 

				activeLength++;
				break; 
			}

			splitEnd = (int*) malloc(sizeof(int)); 
			*splitEnd = next->start + activeLength - 1; 

			Node *split = newNode(next->start, splitEnd, next->docno); 
			activeNode->children[text[next->docno][next->start]] = split; 
 
			split->children[text[docno][pos]] = newNode(pos, &leafEnds[docno], docno); 
			next->start += activeLength; 
			split->children[text[next->docno][next->start]] = next; 

			if (lastNewNode != NULL) 
				lastNewNode->suffixLink = split; 
			
			lastNewNode = split; 
		}

		remainingSuffixCount--; 
		if (activeNode == root && activeLength > 0) {
			activeLength--; 
			activeEdge = pos - remainingSuffixCount + 1; 
		} else if (activeNode != root) {
			activeNode = activeNode->suffixLink; 
		} 
	} 
}

//Function to print parts of a document (text on an edge, eg)
void print(int i, int j, int docno) {
	int k; 
	for (k=i; k<=j; k++) 
		printf("%c", text[docno][k]); 
}

//Function to set the indices of leaves through DFS
void setSuffixIndexByDFS(unsigned char **text , Node *n, int labelHeight) {
	if (n == NULL) return;

	int leaf = 1; 
	int i; 
	for (i = 0; i < MAX_CHAR; i++) {
		if (n->children[i] != NULL) {
			leaf = 0; 
			setSuffixIndexByDFS(text,n->children[i], labelHeight + 
								edgeLength(n->children[i])); 
		} 
	} 
	if (leaf == 1)
		n->suffixIndex = strlen(text[n->docno]) - labelHeight;
}

//Function to free the tree
void freeSuffixTreeByPostOrder(Node *n) {
	if (n == NULL) 
		return; 
	
	int i; 
	for (i = 0; i < MAX_CHAR; i++)
		if (n->children[i] != NULL)
			freeSuffixTreeByPostOrder(n->children[i]);

	if (n->suffixIndex == -1) 
		free(n->end); 
	
	free(n); 
}

//Function to add a unique terminator to a particular document
// Terminator length depends on number of documents.
// Characters in the terminator are outside ASCII range(>=128)
// Hence, unsigned char is used for the text.
// These terminators are appended to the text of the document thereby
// making each document end with a unique terminator.
// To make the terminator for a document, the digits of the documentID are used.
void add_terminator(char *text, int docno) {
	char *str = (char*)calloc(NUM_TERMINATORS, sizeof(char));
	int i;
	for(i=0; i<NUM_TERMINATORS-1; ++i)
		str[i] = 128;
	str[i] = 0;

	int c = 0;
	while(docno>0) {
		str[c] += docno%10;
		c++;
		docno/=10;
	}
	
	int tlen = strlen(text);
	
	int l = strlen(str);
	for(i=0; i<l; ++i)
		text[tlen+i] = str[i];
	
	free(str);
}


void buildSuffixTree(unsigned char ** text) {
	 
	int i,j; 
	rootEnd = (int*) malloc(sizeof(int)); 
	*rootEnd = - 1;
	root = newNode(-1, rootEnd, 0); 
	activeNode = root; 
	for(j=0; j<NUM_DOCS; ++j) {
		add_terminator(text[j], j);
		size = strlen(text[j]);
		for (i=0; i<size; i++) {
			extendSuffixTree(text,i, j); 
		}
		lastNewNode = NULL; 
		activeNode = root; 
		activeEdge = -1; 
		activeLength = 0;  
		remainingSuffixCount = 0;
	}
	int labelHeight = 0; 
	setSuffixIndexByDFS(text,root, labelHeight); 
} 

//Function to traverse an edge to see if str is part of it
int traverseEdge(unsigned char **text,char *str, int idx, int start, int end, int docno) {
    int k = 0;
    for(k=start; k<=end && str[idx] != '\0'; k++, idx++)
        if(text[docno][k] != str[idx]) 
            return -1;

    if(str[idx] == '\0') 
        return 1;

    return 0;
} 
  
//Function to count the number of leaves below a Node n
int doTraversalToCountLeaf(Node *n,int flag) {
	
    if(n == NULL) 
        return 0; 
    if(n->suffixIndex > -1) {
        if(comma_index[n->docno]>n->suffixIndex) {
        	if(flag==1) {		
				check[n->docno].title_count+=1;
			} else {
				check[n->docno].title_count_full+=1;
			}
        } else {
			if(flag==1) {		
				check[n->docno].text_count+=1;
			} else {
				check[n->docno].text_count_full+=1;
			}
        }
        		
        return 1; 
    } 
    int count = 0; 
    int i = 0; 
    for (i = 0; i < MAX_CHAR; i++) { 
        if(n->children[i] != NULL) { 
            count += doTraversalToCountLeaf(n->children[i],flag); 
        } 
    } 
    return count;  
} 
  

int countLeaf(Node *n,int flag) {
    if(n == NULL) 
        return 0; 
    return doTraversalToCountLeaf(n,flag); 
} 



int doTraversal(unsigned char** text ,Node *n, char* str, int idx,int flag) {
    if(n == NULL) {
        return -1; 
    } 
    int res = -1; 
    if(n->start != -1) {
        res = traverseEdge(text,str, idx, n->start, *(n->end), n->docno); 
        if(res == -1)  
            return -1; 
        if(res == 1) { 
            if(n->suffixIndex > -1) {     
				if(comma_index[n->docno]>n->suffixIndex) {
					if(flag==1) {		
						check[n->docno].title_count+=1;
					} else {
						check[n->docno].title_count_full+=1;
					}
				} else {
					if(flag==1) {		
						check[n->docno].text_count+=1;
					} else {
						check[n->docno].text_count_full+=1;
					}
				}	
            } else {
                countLeaf(n,flag); 
            }
            return 1; 
        } 
    } 
    idx = idx + edgeLength(n); 
    if(n->children[str[idx]] != NULL) 
        return doTraversal(text,n->children[str[idx]], str, idx,flag); 
    else
        return -1;   
} 
//Function to search for a particular string str in the generalized suffix tree
void search_substring(unsigned char **text,char* str,int flag) {
    int res = doTraversal(text,root, str, 0,flag);
    
    if(res == -1) 
        printf("-1, \n");
    
} 



void setLeaves(Node *n, int idx, int *pos, int *lens) {
	if(n == NULL) 
        return; 
    
    if(n->suffixIndex > -1) { 
        if(lens[n->docno] < idx) {
    		pos[n->docno] = n->suffixIndex;
    		lens[n->docno] = idx;
    	} else if(lens[n->docno] == idx && pos[n->docno] > n->suffixIndex) {
    		pos[n->docno] = n->suffixIndex;
    	}
        
        return;
    } 
   
    int i = 0; 
    for (i = 0; i < MAX_CHAR; i++) { 
        if(n->children[i] != NULL) {
            setLeaves(n->children[i], idx, pos, lens);
        } 
    } 
    return;
}
  

int lcsTraversal(unsigned char**text,Node *n, char* str, int idx, int *pos, int *lens) {
    if(n == NULL)
        return -1;
    
    int res = -1, i=0;
    if(n->start != -1) {
		for(i=n->start; i<=*(n->end) && str[idx] != '\0' && text[n->docno][i] == str[idx]; ++i, ++idx);

        if(n->suffixIndex > -1) {
        	if(lens[n->docno] < idx) {
        		pos[n->docno] = n->suffixIndex;
        		lens[n->docno] = idx;
        	} else if(lens[n->docno] == idx && pos[n->docno] > n->suffixIndex) {
        		pos[n->docno] = n->suffixIndex;
        	}

        } else{
            setLeaves(n, idx, pos, lens); 
        }
        
       
        if(str[idx] == '\0' || i<=*(n->end))
        	return 1;
        
    }
    if(n->children[str[idx]] != NULL) 
        return lcsTraversal(text,n->children[str[idx]], str, idx, pos, lens); 
    else
        return -1;
} 

int *first_occurance_lcs(unsigned char**text,char *str) {
	int *pos = (int*)calloc(NUM_DOCS, sizeof(int));
	int *lens = (int*)calloc(NUM_DOCS, sizeof(int));

	int i;
	for(i=0; i<NUM_DOCS; ++i) {
		pos[i] = -1;
		lens[i] = -1;
	}
	int idx = 0;
	
	int len = strlen(str);
	for(i=0; i<len; ++i) {
		lcsTraversal(text,root, str + i, 0, pos, lens);
	}
	int j;
	printf("DocNo \t Index \t Length \n");
	for(i=0; i<NUM_DOCS; ++i) {
		printf("%d \t %d \t %d", i+1, pos[i], lens[i]);
		printf("\n");
	}
	return pos;
}

//Function to take input from data file passed. 
int take_input(char *filename) {
	FILE *fp = fopen(filename, "r");
	char *alldocs = (char*)calloc(ALLDOCS_SIZE, sizeof(char));
	fread(alldocs, sizeof(char), ALLDOCS_SIZE, fp);
	
	
	int num = 0;
	int i;
	for(i=0; alldocs[i] != '\0'; ++i)
		if(alldocs[i] == '\n')
			num++;
	comma_index = (int*)malloc(sizeof(int)*num);
	// printf("%d\n", num);
	text = (unsigned char **)calloc(num, sizeof(unsigned char*));
	leafEnds = (int*)calloc(num, sizeof(int));
	unsigned char *temp = NULL;
	temp = strtok(alldocs, "\n");
	int num_digits = 0;
	while(num) {
		num_digits++;
		num/=10;
	}
	NUM_TERMINATORS = num_digits + 1;
	int docs = 0;
	int flag = 1;
	while(temp) {
		text[docs] = (unsigned char *)
		 	calloc(strlen(temp)+NUM_TERMINATORS+10, sizeof(unsigned char));
		
		for(i=0; i<strlen(temp); ++i) {	
			if(temp[i]==',' && flag==1) {
				if(temp[i-1]=='\'') {
					comma_index[docs]=i;
					flag=0;
				}
			}
			text[docs][i] = temp[i];
		}
		
		text[docs][i] = 0;
		docs++;
		flag=1;
		temp = strtok(NULL, "\n");
	}
	return docs;
}

int main(int argc, char *argv[]) {
	if(argc!=2) {
		printf("Please provide only data file as command line argument.\n");
		return -1;
	}
	
	NUM_DOCS = take_input("clean_data_cs.csv");
	if(NUM_DOCS==0) {
		printf("Data file invalid.\n");
		return -1;
	}
	struct timespec start;
	struct timespec end;
	indice =(int**)malloc(sizeof(int*)*NUM_DOCS);
    check = (relevance_count*)malloc(sizeof(relevance_count)*NUM_DOCS);
    clock_gettime(CLOCK_REALTIME,&start);
	buildSuffixTree(text);
	clock_gettime(CLOCK_REALTIME,&end);
	printf("%f \n",time_elapsed(&start,&end));
	int t;
	scanf("%d", &t);
	int i;
	char str[MAX_SEARCH_SUBSTRING_SIZE];
	int *pos;
	char *temp;

	for(i=0; i<t; ++i) {
		 for(int i = 0 ; i < NUM_DOCS ; i++) {
    		indice[i]=(int*)malloc(sizeof(int)*10000);
 			check[i].text_count = 0;
 			check[i].title_count = 0;
 			check[i].docno= i;
 			check[i].score = 0 ;
 			check[i].title_count_full=0;
 			check[i].text_count_full=0;
    	} 
		getchar();
		scanf("%[^\n]", str);
		// printf("STR %s\n", str)
		clock_gettime(CLOCK_REALTIME,&start);
		if(*argv[1]=='1') {
			pos = first_occurance_lcs(text,str);
		} else {
			search_substring(text,str,0);
			printf("For relevance string is %s\n",str);
			temp = strtok(str," ");
			while(temp) {	
				search_substring(text,temp,1);
				temp=strtok(NULL," ");
			}

			for(int i = 0 ; i < NUM_DOCS ; i++) {
    			check[i].score = 40 * check[i].text_count_full + 60 * check[i].title_count_full + 1 * check[i].text_count + 2 * check[i].title_count;
    		
   			}
			quickSort(0,NUM_DOCS-1);

			printf("DocumentNumber RelevanceScore TitleSubstringNo TextSubstringNo TitleStringNo TextStringNo\n");
			for(int i = 0 ; i < 10 ; i++) {
    			printf("%d \t\t %d \t\t %d  \t\t %d  \t\t %d  \t\t %d\n",check[i].docno,check[i].score,check[i].title_count,check[i].text_count,check[i].title_count_full,check[i].text_count_full);
    			
    		}
		}
		
		clock_gettime(CLOCK_REALTIME,&end);
		printf("%f \n",time_elapsed(&start,&end));

	}

	freeSuffixTreeByPostOrder(root);

	return 0; 
}
double time_elapsed(struct timespec *start, struct timespec *end) {
	double t;
	t = (end->tv_sec - start->tv_sec); // diff in seconds
	t += (end->tv_nsec - start->tv_nsec) * 0.000000001; //diff in nanoseconds
	return t;
}