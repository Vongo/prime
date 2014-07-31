#include <stdint.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define MAX_FACTORS 64 // Nombre maximum de facteurs premiers d'une décomposition
#define MAX_PRIME 150000 // Nombre des premiers nombres premiers séquentiels stockés
#define MAX_THREAD 8 // Nombre de threads lancés par le programme
#define PRIME_STEP 1 // Largeur du pas lors du calcul fainéant des premiers nombres premiers 
#define LINE_LENGTH 21 // Longueur maximale d'une ligne du fichier source
#define PRIME_TOLERANCY 10000 // Nombre maximal de nombres premiers utiles stockés en plus des MAX_PRIME premiers
#define HASH_DEPTH 10000 // Largeur de chacun des algorithmes de hachage

#define MEMOI // Permet d'activer ou non la mémoisation des décompositions effectuées.

// Structure de stockage d'une décomposition en produits de facteurs premiers.
typedef struct Dec
{
	uint64_t root; // Nombre à décomposer
	uint64_t* dive; // Diviseurs premiers connus (initialisé à MAX_FACTORS unités)
	struct Dec* dec; // Pointeur vers une autre décomposition connue
}Dec;

// Liste simplement chaînée stockant les décompositions connues (après hachage).
typedef struct List
{
	Dec laDec;
	struct List *next;
} List;

// Déclaration en mémoire de la table stockant les décompositions connues.
static List* glEdhec[HASH_DEPTH][HASH_DEPTH];

pthread_mutex_t mtx_gnb; // Mutex protégeant l'accès au curseur de lecture du fichier
pthread_mutex_t mtx_screen; // Mutex protégeant l'accès à l'écran
pthread_mutex_t mtx_primelist; // Mutex protégeant l'accès en écritur à la liste des nombres premiers connus
pthread_mutex_t mtx_globalz; // Mutex protégeant l'accès en écriture aux autres variables globales
pthread_mutex_t mtx_memoi; // Mutex protégeant l'accès en écriture à la table des décompositions connues

static FILE* gf; // Fichier à lire
static uint64_t gtPrime[MAX_PRIME+PRIME_TOLERANCY]; // Table des nombres premiers connus
static int giExploredSoFar; // Curseur indiquant le nombre de nombres premiers connus
static uint64_t gi, gj, gessai, gk, gsommet, gnb; // Variables d'environnement nécessaires au calcul fainéant
// des PRIME_STEP prochains nombres premiers (dans fPrimeTill() et gPrimeTill()).
static uint64_t *gm, *gdp; // Idem.
static int gMaxPrime = (MAX_PRIME-1); // Curseur dynamique désignant la plus grande valeur calculable dans le tableau des nombres premier connus.

void Print(Dec pD)
// Procédure récursive permettant d'afficher à l'écran les décompostions successives d'un nombre donné.
{
	int i = 0;
	if(pD.dive[i] != 0)
		while (pD.dive[i] != 0 || pD.dec != NULL)
		{
			printf(" %llu",(long long) pD.dive[i++]);
			if(pD.dec != NULL)
				Print(*(pD.dec));
		}
	else
		if(pD.dec != NULL)
				Print(*(pD.dec));
}

void sPrint(Dec pD)
// Procédure permettant d'initialiser l'affichage à l'écran des décompositions successives d'un nombre.
{
	printf("%llu :",(long long) pD.root);
	Print(pD);
	printf(".\n");
}

void gPrimeTill (int pnbPlus)
// Permet de calculer pnbPlus nombre(s) premier(s) supplémentaire(s) séquentiel(s).
{
	int vToExplore = giExploredSoFar + pnbPlus;
	for(; giExploredSoFar < vToExplore; gi+=gk, gk=6-gk)
	{
		for(gessai = gdp[gj]; (gi!=gm[gj])&&(gessai*gessai)<gi; gessai=gdp[++gj])
		{
			if(gi>gm[gj])
			{
				gm[gj] += 2*gessai;
			}
		}
		if (gi!=gm[gj])
		{
			gtPrime[giExploredSoFar++] = gi;
			gdp[gsommet]=gi;
			gm[gsommet++]=gi*gi;
		}
	}
}

void fPrimeTill (uint64_t max)
// Permet de calculer les nombres premiers non connus jusqu'à max.
{
	for(; gi<max; gi+=gk, gk=6-gk)
	{
		for(gessai = gdp[gj]; (gi!=gm[gj])&&(gessai*gessai)<gi; gessai=gdp[++gj])
		{
			if(gi>gm[gj])
			{
				gm[gj] += 2*gessai;
			}
		}
		if (gi!=gm[gj])
		{
			gtPrime[giExploredSoFar++] = gi;
			gdp[gsommet]=gi;
			gm[gsommet++]=gi*gi;
		}
	}
}

void u_print_prime_factors()
// Cette procédure est appelée par chacun des threads qui liront, chacun de son côté, 
// le fichier gf à la recherche de nombres à décomposer. 
{
	int j, i;
	char line[LINE_LENGTH];
	uint64_t nn;
	unsigned int i1, i2;
	short int vKnown;

	while(fgets(line, LINE_LENGTH, gf) != NULL)
	{
		// Boucle de lecture du fichier. Une itération correspond à une ligne donc à un nombre.
		j = 0;
		i = 0;
		vKnown = 0;

		pthread_mutex_lock(&mtx_gnb);
		sscanf (line, "%llu", (long long unsigned int*) &gnb);
		nn = (uint64_t) gnb;
		pthread_mutex_unlock(&mtx_gnb);

		Dec uD;
		uD.root = nn;
		uD.dive = calloc(MAX_FACTORS, sizeof(uint64_t));
		uD.dec = NULL;

		while (i<=giExploredSoFar && nn !=1) 
		{
#ifdef MEMOI
			i1 = (nn%HASH_DEPTH);
			i2 = ((nn/HASH_DEPTH)%HASH_DEPTH);
/***************************************SECTION CRITIQUE**************************************************/
			// Cherche si la décomposition de nn a déjà été efectuée.
			pthread_mutex_lock(&mtx_memoi);
			List* uL = glEdhec[i1][i2];
			if (uL != NULL)
			{
				if (uL->laDec.root == nn)
				{
					uD.dec = &(uL->laDec);
					vKnown = 1;
					pthread_mutex_unlock(&mtx_memoi);
					break;
				}
				while (uL->next != NULL)
				{
					uL = uL->next;
					if (uL->laDec.root == nn)
					{
						uD.dec = &(uL->laDec);
						vKnown = 1;
						break;
					}
				}
				if (vKnown==1)
				{
					pthread_mutex_unlock(&mtx_memoi);
					break;
				}
			}
			pthread_mutex_unlock(&mtx_memoi);
/***********************************FIN SECTION CRITIQUE**************************************************/
#endif
			if (i >= gMaxPrime-1)
			{
				// Dans le cas où on n'a pas trouvé de facteur dans la liste des nombres premiers connus, 
				// on passe en "mode manuel" : on cherche de manière intelligente de nouveaux facteurs. 
				if(nn!=1)
				{
					//***************************//
					//         Subtilité         //
					//***************************//
					uint64_t li, lj, lessai, lk, lsommet;
					static uint64_t *lm, *ldp;
/***************************************SECTION CRITIQUE**************************************************/
					//On récupère le contexte des fonctions partagées de recherche de nombres premiers.
					pthread_mutex_lock(&mtx_gnb);
					li = gi;
					lj = gj;
					lessai = gessai;
					lk = gk;
					lsommet = gsommet;
					lm = gm;
					ldp = gdp;
					pthread_mutex_unlock(&mtx_gnb);
/***********************************FIN SECTION CRITIQUE**************************************************/
					uint64_t vMaxx = sqrt(nn);
					for(; nn > 1 && li<vMaxx; li+=lk, lk=6-lk)
					{
						if (!(nn%li))
						{
							for(lessai = ldp[lj]; (li!=lm[lj])&&(lessai*lessai)<li; lessai=ldp[++lj])
							{
								if(li>lm[lj])
								{
									lm[lj] += 2*lessai;
								}
							}
							if (li!=lm[lj])
							{
/***************************************SECTION CRITIQUE**************************************************/
								// Si on trouve un facteur premier, on l'ajoute à la liste des
								// facteurs premiers connus.
								if(giExploredSoFar+1 < MAX_PRIME+PRIME_TOLERANCY)
								{								
									pthread_mutex_lock(&mtx_primelist);
									gtPrime[giExploredSoFar++] = li;
									pthread_mutex_unlock(&mtx_primelist);
								}
/***********************************FIN SECTION CRITIQUE**************************************************/
								// On cherche un facteur suivant.
								gMaxPrime++;
								uD.dive[j++] = li;
								nn /= gtPrime[i];
								ldp[lsommet]=li;
								lm[lsommet++]=li*li;
							}
						}
					}
					if (li>=vMaxx)
						uD.dive[j++]=nn;
					/*****************************/
				}
				break;
			}
			else
			{
				// On est dans le cas normal, on parcourt la liste des nombres premiers connus
				// à la recherche d'un facteur
				if (gtPrime[i]==0)
				{
					uint64_t vMaxx = sqrt(nn);	
					if (gtPrime[i-1] > vMaxx) 
					{
						uD.dive[j++] = nn;
						break;
					}
					pthread_mutex_lock(&mtx_primelist);
					gPrimeTill(PRIME_STEP);
					pthread_mutex_unlock(&mtx_primelist);
				}
				while(!(nn%gtPrime[i]))
				{
					// Quand un facteur est facteur plusieurs fois, on l'enregistre plusieurs fois.
					uD.dive[j++] = gtPrime[i];
					nn /= gtPrime[i];
				}
				i++;
			}
		}
		if (j==0 && uD.dec == NULL) 
		{
			// On n'a pas trouvé de facteur premier inférieur à la racine du nombre
			// et on n'a pas déjà décomposé le nombre.
			// De ce fait, le nombre est déclaré premier et enregistré comme tel.
			pthread_mutex_lock(&mtx_primelist);
			gtPrime[giExploredSoFar++] = nn;
			pthread_mutex_unlock(&mtx_primelist);
			uD.dive[j++] = nn;
		}
		if (j!=0)
		{
			// Si cette décomposition apporte un élément nouveau, on memoise
			// la décomposition complète du nombre en cours de traitement.
#ifdef MEMOI
			i1 = (uD.root%HASH_DEPTH);
			i2 = ((uD.root/HASH_DEPTH)%HASH_DEPTH);
			List* nouvo = malloc(sizeof(List));
			nouvo->laDec = uD;
			nouvo->next = NULL;		
			pthread_mutex_lock(&mtx_memoi);
			List* uL = glEdhec[i1][i2];
			if (uL != NULL)
			{
				while (uL->next != NULL && uL->laDec.root != uD.root)
				{
					uL = uL->next;
				}
				if (uL->next == NULL && uL->laDec.root != uD.root)
					uL->next = nouvo;
			}
			else
				glEdhec[i1][i2] = nouvo;
			pthread_mutex_unlock(&mtx_memoi);
		}
#endif
		/*/ À commenter pour ne pas imprimer les décompositions.
		pthread_mutex_lock(&mtx_screen);
		sPrint(uD);
		pthread_mutex_unlock(&mtx_screen);
		//*/
	}
}

void ginit()
// Initialise les variables d'environnement et effectue les allocations en mémoire.
{
	gm = calloc(MAX_PRIME, sizeof(uint64_t));
	gdp = calloc(MAX_PRIME, sizeof(uint64_t));
	gtPrime[0] = 2;
	gtPrime[1] = 3;
	gtPrime[2] = 5;
	giExploredSoFar = 3;
	gk = 4;
	gm[0] = 25;
	gdp[0] = 5;
	gsommet = 1;
	gi = 7;
	gj = 0;
	// Initialise le tableau des nombres premiers.
	fPrimeTill(50);
	gPrimeTill(PRIME_STEP);
}

int main()
{
	ginit();

	int i, j;
	pthread_t t[MAX_THREAD];
	gf = fopen ("numbers.txt", "rt");

	for (i=0; i<MAX_THREAD; i++)
	{ // Lance MAX_THREADS threads.
		pthread_create(&t[i], NULL, (void*)&u_print_prime_factors, NULL);
		pthread_mutex_lock(&mtx_screen);
		printf("%i thread(s) lancé(s).\n", i+1);
		pthread_mutex_unlock(&mtx_screen);
	}

	for (i=0; i<MAX_THREAD; i++)
	{ // Attend l'arrêt des threads lancés.
		pthread_join(t[i], NULL);
		pthread_mutex_lock(&mtx_screen);
		printf("%i thread(s) arrêté(s).\n", i+1);
		pthread_mutex_unlock(&mtx_screen);
	}
	fclose(gf);

	printf("\nNous connaissons désormais %i nombres premiers.\n", giExploredSoFar);
	printf("Notre plus grand nombre premier connu est : %llu\n", (long long unsigned) gtPrime[giExploredSoFar-1]);

	free (gdp);
	free (gm);
	return 0;
}
