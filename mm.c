/* Kamil Puchacz, nr indexu: 309593
 * Oświadczam, że jestem jedynym autorem kodu źródłowego.
 *
 * Wyszczególnione procedury zostały zaczerpnięte (oraz w niektórych przypadkach
 * zmodyfikowane) z przykładowego rozwiązania wykładowcy(plik mm-implicit.c):
 * bt_size, bt_used, bt_free, bt_footer, bt_fromptr, bt_make_footer,
 * bt_get_prevfree, bt_clr_prevfree, bt_payload, bt_next, bt_prev
 *
 * Opis zajętego bloku:
 * -zajęty blok ma rozmiar minimum 16 bajtów, lub większy(wielokrotnośc 16
 * bajtów) -zawiera na początku header, w którym jest zapisany rozmiar
 * danego bloku, 1 na pierwszym bicie(w pierwszym bicie jest przechowywana
 * informacja czy blok jest zajęty(1) czy wolny(0)), oraz 0 lub 1 na drugim
 * bicie(na drugim bicie zapisujemy informację czy poprzedni blok jest wolny(1)
 * czy jest zajęty(0)) -po 4 bajtach poswięconych na header, zaczyna się
 * payload, pierwszy bajt pamięci udostępniony użytkownikowi.
 *
 * Opis wolnego bloku:
 * -wolny blok ma rozmiar minimum 16 bajtów
 * -zawiera na początku header zajmujący 4 bajty, w którym
 * jest zapisany rozmiar danego bloku, 0 na pierwszym bicie(w pierwszym bicie
 * jest przechowywana informacja czy blok jest zajęty(1) czy wolny(0)) -po
 * headerze jest umiejscowiony względny wskaźnik(wartość odległość względem
 * heap_start(adres pierwszego bloku)) zajmujący 4 bajty do poprzedniego wolnego
 * bloku z danej klasy, jeśli takiego nie ma to jest zapisana tam wartość -1
 * (taki odpowiednik NULL) -następnie, jest umiejscowiony względny
 * wskaźnik do następnego wolnego bloku z danej klasy, jeśli takiego
 * nie ma to jest zapisana tam wartość -1 -ostatnie 4
 * bajty danego bloku są przeznaczone na footer(drugi nagłówek)
 *
 * wysokopoziomowy opis działania przydziału bloku:
 * procedura malloc najpierw spróbuje znaleźć wolny blok wymaganego rozmiary w
 * odpowiednich klasach wolnych bloków.(jeśli taki znajdzie to go zwolni z list
 * wolnych bloków. Jeśli jest za duży to uruchomi na nim split) Jeśli to
 * zawiedzie to sprawdzi sytuacje przegowe(ostatni blok wolny, ale za mały,
 * wtedy powiększamy tylko o brakujące miejsce, itp.). Jeśli nie znajdzie
 * żadnego wolnego bloku to alokuje cały nowy blok powiększając sterte.
 *
 * wysokopoziomowy opis działania zwalniania bloku:
 * -Oznaczamy zwalniany blok jako wolny
 * -Sprawdzamy czy poprzednik jest wolny, jeśli tak to usuwamy go z klas wolnych
 * bloków oraz łaczymy z obecnie zwalnianym blokiem -Sprawdzamy czy następnik
 * jest wolny, jeśli tak to usuwamy go z klas wolnych bloków oraz łaczymy z
 * obecnie zwalnianym blokiem -wrzucamy blok do określonej klasy wolnych bloków,
 * ustawiamy w bloku następnym po nim, że poprzednik jest wolny
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define classes 8       /*  liczba klas wolnych blokóœ */
typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *segregated_list; /* wskaznik na poczatek listy klas */
static word_t *heap_start;      /* Address of the first block */
static word_t *last;            /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */
static inline size_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}
/* zwraca informacje czy dany blok jest używany */
static inline int bt_used(word_t *bt) {
  return *bt & USED;
}
/*  zwraca informacje czy dany blok jest wolny */
static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}
/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (word_t *)((void *)bt + bt_size(bt) - sizeof(word_t));
}
/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}
static inline void bt_make_footer(word_t *bt) {
  word_t *footer = bt_footer(bt);
  *footer = *bt;
}
/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}
/* ustawia 0 na drugim bicie headera danego bloku, czyli informację, że
 * poprzedni blok jest zajety */
static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}
/* ustawia 1 na drugim bicie headera danego bloku, czyli informację, że
 * poprzedni blok jest wolny */
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}
/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}
/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt == last)
    return NULL;
  return (void *)bt + bt_size(bt);
}
/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start)
    return NULL;
  return (void *)bt - bt_size(bt - 1);
}
static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}
static inline void set_header(word_t *block, size_t size, bool is_allocated) {
  *block = size | is_allocated;
}
/* Określa klasę z której możemy wyciągnąć bok o żądanym rozmiarze */
static inline word_t *set_class_to_get_free_block(size_t size) {
  size_t size_class = 16;
  for (int i = 0; i < classes; i++) {
    if (size_class >= size)
      return (void *)segregated_list + i * sizeof(word_t);
    size_class *= 2;
  }
  return (void *)segregated_list + (classes - 1) * sizeof(word_t);
}
/* Przechodzimy do klasy wyższej, która wskazuje na pierwszy
 * element z listy klasy wyższej lub null jesli pusta  */
static inline word_t *get_next_class(word_t *class) {
  class += 1;
  if (class >= segregated_list + classes)
    return NULL;
  return class;
}
/* Określa klasę, do której mamy wstawić dany blok */
static inline word_t *set_class_to_insert_free_block(word_t *block) {
  size_t size = bt_size(block);
  size_t size_class = 16;
  for (int i = 0; i < classes; i++) {
    if (size_class == size)
      return segregated_list + i;
    if (size_class > size)
      return segregated_list + (i - 1);
    size_class *= 2;
  }
  return segregated_list + (classes - 1);
}
/* Ustawia wskaźnik w bieżącym wolnym bloku na kolejny wolny blok należący do
  wspólnej klasy */
static inline void set_next_free_block(word_t *block, word_t *next_free_block) {
  if (block == NULL)
    return;
  if (next_free_block == NULL)
    *(block + 2) = -1;
  else
    *(block + 2) = next_free_block - heap_start;
}
/* Ustawia wskaźnik w bieżącym wolnym bloku na poprzedni wolny blok należący do
  wspólnej klasy */
static inline void set_prev_free_block(word_t *block, word_t *prev_free_block) {
  if (block == NULL)
    return;
  if (prev_free_block == NULL)
    *(block + 1) = -1;
  else
    *(block + 1) = prev_free_block - heap_start;
}
/* Pobiera wskaznik na następny wolny blok z klasy względem bieżacego bloku */
static inline word_t *get_next_free_block(word_t *block) {
  if (*(block + 2) == -1)
    return NULL;
  else
    return (word_t *)((unsigned long)*(block + 2) + heap_start);
}
/* Pobiera wskaznik na poprzedni wolny blok z klasy względem bieżacego bloku */
static inline word_t *get_prev_free_block(word_t *block) {
  if (*((word_t *)block + 1) == -1)
    return NULL;
  else
    return (word_t *)((unsigned long)*(block + 1) + heap_start);
}
/* Pobiera pierwszy wolny blok z danej klasy */
static inline word_t *get_first_free_block_from_class(word_t *class) {
  word_t addr = *class;
  if (addr == -1)
    return NULL;
  else
    return heap_start + (unsigned long)addr;
}
/* Wkłada wolny blok do określonej za pomocą set_class_to_insert_free_block
 * klasy w porządku rosnącym względem rozmiaru */
static inline void insert_free_block_to_segregated_list(word_t *block) {
  word_t *class = set_class_to_insert_free_block(block);
  word_t *head_list = get_first_free_block_from_class(class);
  size_t size_inserted_block = bt_size(block);
  if (head_list == NULL) {
    /* klasa jest pusta, wkładamy wolny blok na początek klasy */
    set_prev_free_block(block, NULL);
    set_next_free_block(block, NULL);
    *class = block - heap_start;
  } else if (size_inserted_block <= bt_size(head_list)) {
    /* głowa klasy ma rozmiar większy od wkładanego bloku, dlatego wkładamy blok
     * na początek klasy */
    set_prev_free_block(block, NULL);
    set_prev_free_block(head_list, block);
    set_next_free_block(block, head_list);
    *class = block - heap_start;
  } else {
    /* szukamy iteracyjnie docelowego miejsca dla danego wolnego bloku */
    word_t *curr_block = head_list;
    word_t *next_block = get_next_free_block(curr_block);
    while (next_block != NULL && bt_size(next_block) < size_inserted_block) {
      curr_block = next_block;
      next_block = get_next_free_block(curr_block);
    }
    set_prev_free_block(next_block, block);
    set_next_free_block(block, next_block);
    set_prev_free_block(block, curr_block);
    set_next_free_block(curr_block, block);
  }
}
/* Zwraca pierwszy wolny blok z danej klasy oraz go usuwa z niej */
static inline word_t *pop_free_block_from_class(word_t *class) {
  word_t *first_free_block_from_class = get_first_free_block_from_class(class);
  if (first_free_block_from_class != NULL) {
    word_t *next_free_block_from_class =
      get_next_free_block(get_first_free_block_from_class(class));
    if (next_free_block_from_class == NULL)
      *class = -1;
    else
      *class = next_free_block_from_class - heap_start;
    set_prev_free_block(get_first_free_block_from_class(class), NULL);
  }
  return first_free_block_from_class;
}
/* Ustawia nagłówek bieżącego bloku, zajęty czy wolny. Sstawia flagi czy
 * poprzedni wolny blok czy zajęty, ustawia w następnym sąsiednim bloku
 * informacje w headerze jesli obecny blok jest zwalniany*/
static inline void set_block(word_t *block, bt_flags is_allocated,
                             size_t size) {
  bt_flags prevfree = bt_get_prevfree(block);
  set_header(block, size, is_allocated);
  if (prevfree) {
    bt_set_prevfree(block);
  }
  if (is_allocated) {
    word_t *next_block = bt_next(block);
    if (next_block != NULL) {
      bt_clr_prevfree(next_block);
    }
  } else {
    bt_make_footer(block);
    word_t *next_block = bt_next(block);
    if (next_block != NULL)
      bt_set_prevfree(next_block);
  }
}
/* dzieli dany blok na dwa.
Jeden o szukanym rozmiarze, ustawia jako zajęty za pomocą set_block.
kolejny po nim, ustawia jako wolny a następnie wsadza go do list wolnych
bloków*/
static inline word_t *split(word_t *block, size_t reqsize) {
  size_t size_found_block = bt_size(block);
  if (block == last)
    last = (word_t *)((void *)block + reqsize);
  set_block(block, true, reqsize);
  word_t *free_block = bt_next(block);
  set_block(free_block, false, size_found_block - reqsize);
  insert_free_block_to_segregated_list(free_block);
  return block;
}

/* Łączy dwa bloki w jeden */
static inline word_t *coalesce(word_t *prev_block, word_t *next_block,
                               bool is_allocated) {
  size_t size = bt_size(prev_block) + bt_size(next_block);
  set_block(prev_block, is_allocated, size);
  if (next_block == last)
    last = (word_t *)prev_block;
  return prev_block;
}
/* Usuwa dany blok z określonej klasy wolnych bloków. Jeśli dany blok jest
  pierwszym blokiem w klasie to go zdejmuje za pomocą pop_free_block_from_class.
  W przeciwnym przypadku, zamienia następniki i poprzedniki u swoich sąsiadów z
  danej klasy wolnych bloków */
static inline void remove_free_block_from_segregated_list(word_t *block) {
  word_t *class = set_class_to_insert_free_block(block);
  if (get_first_free_block_from_class(class) == block) {
    pop_free_block_from_class(class);
    return;
  }
  word_t *next_block = get_next_free_block(block);
  word_t *prev_block = get_prev_free_block(block);
  set_prev_free_block(next_block, prev_block);
  set_next_free_block(prev_block, next_block);
}
/* Ustawia dany blok znajdujący sie w klasach wolnych bloków jako obecnie
 * wykorzystywany oraz go usuwa stamtąd*/
static inline void set_free_block_from_segregated_list_as_used(word_t *block) {
  remove_free_block_from_segregated_list(block);
  set_block(block, true, bt_size(block));
}
/* znajduje odpowiednich rozmiarów wolny blok z dnaje klasy oraz ustawia jego
 * użycie. Jesli znajdzie większy - podzieli go za pomocą split*/
static inline word_t *take_free_block_from_class(word_t *class, size_t size) {
  word_t *block = get_first_free_block_from_class(class);
  while (true) {
    if (block != NULL && bt_size(block) == size) {
      /*  Jeśli znaleziony blok jest dokładnie wymaganych rozmiarów, zwalnia go
       * z list wolnych bloków oraz ustawia jako używany  */
      set_free_block_from_segregated_list_as_used(block);
      return block;
    }
    if (block != NULL && bt_size(block) > size) {
      /* Jeśli jest większy niż znaleziony to ustawia dany blok jako używany, a
       * następnie uruchamia na nim split*/
      set_free_block_from_segregated_list_as_used(block);
      return split(block, size);
    } else if (block != NULL)
      block = get_next_free_block(block);
    else
      return NULL;
  }
}
/* Zwraca blok o wymaganym rozmiarze z klas wolnych bloków. Jeśli bieżąca klasa
 * jest pust - przechodzi do wyższych*/
static inline word_t *take_free_block_from_segregated_list(size_t size) {
  word_t *class = set_class_to_get_free_block(size);
  word_t *block = NULL;
  while (class != NULL && block == NULL) {
    block = take_free_block_from_class(class, size);
    if (block != NULL) {
      return block;
    } else
      class = get_next_class(class);
  }
  return NULL;
}
/* inicjujemy wskazniki w klasach wartością null(-1). Używamy tu adresów
 * względnych */
static inline void init_segredated_list() {
  for (int i = 0; i < classes; i++)
    *(segregated_list + i) = -1;
}
/* powiększa stertę o wymagany rozmiar pamięci.*/
static inline void *morecore(size_t size) {
  word_t *block = mem_sbrk(size);
  if (block == (void *)-1)
    return NULL;
  return block;
}

int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  size_t size_segregated_list = classes * sizeof(word_t);
  segregated_list = mem_sbrk(size_segregated_list);
  if ((long)segregated_list < 0)
    return -1;

  if (size_segregated_list % 16 != 12) {
    if (morecore(12 - size_segregated_list % 16) == NULL)
      return -1;
  }
  init_segredated_list();
  heap_start = NULL;
  last = NULL;
  return 0;
}

/* Zwraca blok pamięci o wymaganym rozmiarze.
 * Jeśli jest to pierwsze wywołanie(last==null), Wtedy po prostu prosimy o nową
 * pamiec za pomocą morecore. Jeśli drugie lub
 * kolejne, to wtedy zawsze najpierw będzie próbowało znaleźć wymagany
 * rozmiar bloku z klasy wolnych bloków. Jeśli nie znajdzie wolnego bloku w
 * klasach wolnych bloków to sprawdzi jeszcze kilka warunków(może zajść
 * sytuacja, że dany blok jest niewystarczająco wielki by sie zakwalifikować do
 * klasy stopień wyżej, od której zaczyna się wyszukiwanie danego rozmiaru
 * bloku)
 * */
void *malloc(size_t size) {
  if (size == 0)
    return NULL;
  word_t *block = NULL;
  size = round_up(sizeof(word_t) + size);
  if (last != NULL) {
    block = take_free_block_from_segregated_list(size);
    if (block)
      return bt_payload(block);
  }
  if (last == NULL ||
      bt_used(last)) { /* jeśli ostatni blok jest zajęty(lub jest to pierwsze
                          wywołanie malloca) to alokujemy pamięć na nowy blok */
    block = morecore(size);
    if (block == NULL)
      return NULL;
    if (heap_start == NULL)
      heap_start = block;
    last = block;
    set_header(block, size, true);
    return bt_payload(block);
  }
  size_t size_last = bt_size(last);
  if (size_last > size) { /*  ostatni blok jest wolny i romiaru większego -
             uruchamiamy split na nim i zwracmy blok użytkownikowi */
    set_free_block_from_segregated_list_as_used(last);
    block = split(last, size);
  } else if (size_last == size) { /* jeśli ostatni blok jest równy i wolny
                                      od szukanego, rejestrujemy jesgo użycie
                                      i zwracamy użytkownikowi */
    set_free_block_from_segregated_list_as_used(last);
    block = last;
  } else { /* jeśli ostatni blok jest wolny, ale za mały, wywołujemy metode
              morecore, następnie łączymy dane dwa bloki w jeden */
    size_t size_new_block = size - size_last;
    block = morecore(size_new_block);
    if (block == NULL)
      return NULL;
    set_free_block_from_segregated_list_as_used(last);
    word_t *last_block = last;
    last = block;
    set_header(block, size_new_block, true);
    block = coalesce(last_block, block, true);
  }
  return bt_payload(block);
}

/* zwalniamy dany blok, sprawdzamy sąsiadów, czy są blokami wolnymi, jeśli tak,
 * to złączamy się z nimi. Następnie wrzucamy dany blok do klasy wolnych bloków
 */
void free(void *ptr) {
  if (ptr == NULL)
    return;
  word_t *current_block = bt_fromptr(ptr);
  set_block(current_block, false, bt_size(current_block));

  if (bt_get_prevfree(current_block)) {
    word_t *preview_block = bt_prev(current_block);
    remove_free_block_from_segregated_list(preview_block);
    current_block = coalesce(preview_block, current_block, false);
  }

  word_t *next_block = bt_next(current_block);
  if (next_block != NULL && bt_free(next_block)) {
    remove_free_block_from_segregated_list(next_block);
    current_block = coalesce(current_block, next_block, false);
  }

  insert_free_block_to_segregated_list(current_block);
}
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *current_block = bt_fromptr(old_ptr);
  size_t size_curr_block = bt_size(current_block);
  size_t reqsize = round_up(size + sizeof(word_t));

  if (reqsize == size_curr_block)
    return old_ptr;
  /* wymagany nowy rozmiar, jest mniejszy od obecnego, wtedy uruchamia się split
   * na bieżącym bloku */
  if (reqsize < size_curr_block) {
    split(current_block, reqsize);
    return old_ptr;
  }

  word_t *next_block = bt_next(current_block);
  /* Sprawdzamy czy po bieżącym bloku występuje kolejny, wolny */
  /* Jeśli suma rozmiaru obecnego i kolejnego bloku jest mniejsza od wymaganego
   * rozmiaru oraz jeśli następny blok jest ostatnim na stercie, wtedy łączymy
   * te dwa bloki, przydzielamy brakujące miejsce za pomocą morecore a następnie
   * znów łączymy*/
  if (next_block != NULL && bt_free(next_block) &&
      size_curr_block + bt_size(next_block) < reqsize && next_block == last) {
    set_free_block_from_segregated_list_as_used(next_block);
    current_block = coalesce(current_block, next_block, true);

    size_t size_new_block = reqsize - bt_size(current_block);
    word_t *new_block = morecore(size_new_block);
    if (new_block == NULL)
      return NULL;
    last = new_block;
    set_header(new_block, size_new_block, true);
    coalesce(current_block, new_block, true);
    return old_ptr;
  }
  /* Sprawdzamy czy po bieżącym bloku występuje kolejny, wolny */
  /* Jeśli suma rozmiaru obecnego i kolejnego bloku jest wieksza od wymaganego
   * rozmiaru, wtedy łączymy te dwa bloki a następnie dzielimy je w odpowiedni
   * sposób*/
  else if (next_block != NULL && bt_free(next_block) &&
           size_curr_block + bt_size(next_block) > reqsize) {
    set_free_block_from_segregated_list_as_used(next_block);
    current_block = coalesce(current_block, next_block, true);
    split(current_block, reqsize);
    return old_ptr;
  }
  /* Sprawdzamy czy po bieżącym bloku występuje kolejny, wolny */
  /* jeśli suma rozmiarów bloków jest równa wymaganamu, wtedy po prostu obydwa
      bloki łaćzymy ze sobą*/
  else if (next_block != NULL && bt_free(next_block) &&
           size_curr_block + bt_size(next_block) == reqsize) {
    set_free_block_from_segregated_list_as_used(next_block);
    coalesce(current_block, next_block, true);
    return old_ptr;
  }
  /* Jesli bieżący blok jest ostatni, wtedy uruchamiamy memcore w celu
     przydzielenia brakującego miejsca, inicjujujemy nowy blok, następnie
     łaczymy obydwa bloki w jeden*/
  else if (next_block == NULL) {
    size_t size_new_block = reqsize - size_curr_block;
    word_t *new_block = morecore(size_new_block);
    if (new_block == NULL)
      return NULL;
    last = new_block;
    set_header(new_block, size_new_block, true);
    coalesce(current_block, new_block, true);
    return old_ptr;
  }

  void *new_ptr = malloc(size);

  if (!new_ptr)
    return NULL;

  /* jeśli żadne poprzednie przypadki nie zaszły, wtedy szukamy całkowicie
   * nowego bloku i kopiujemy dane*/
  word_t *block = bt_fromptr(old_ptr);
  size_t old_size = bt_size(block) - sizeof(word_t);
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* Sprawdza czy blok znaduje sie w klasie(docelowej) wolnych bloków */
static inline word_t *find_in_segregated_list(word_t *block) {
  word_t *class = set_class_to_insert_free_block(block);
  word_t *found_block = get_first_free_block_from_class(class);
  while (true) {
    if (found_block == block)
      return block;
    else if (found_block != NULL)
      found_block = get_next_free_block(found_block);
    else
      return NULL;
  }
}
/* Wypisuje stan menadżera pamięci */
static inline void list_the_contents_of_the_heap() {
  printf("list of all blocks:\n");
  word_t *block = heap_start;
  while (block != NULL) {
    printf("used?=%d, prev-free?=%d, Block_size=%ld, addres=%p\n",
           bt_used(block), bt_get_prevfree(block), bt_size(block), block);
    block = bt_next(block);
  }
  printf("list of free blocks:\n");
  word_t *class = segregated_list;
  block = get_first_free_block_from_class(class);
  while (true) {
    if (block != NULL) {
      printf("Block_size=%ld, addres=%p\n", bt_size(block), block);
      block = get_next_free_block(block);
    } else if (block != NULL)
      block = get_next_free_block(block);
    else {
      class = get_next_class(class);
      if (class == NULL)
        break;
      else
        block = get_first_free_block_from_class(class);
    }
  }
}
void mm_checkheap(int verbose) {

  // Każdy blok na liście wolnych bloków jest oznaczony jako wolny:
  word_t *class = segregated_list;
  word_t *block = get_first_free_block_from_class(class);
  while (true) {
    if (block != NULL && bt_used(block)) {
      printf("zajety blok na liscie wolnych\n");
      list_the_contents_of_the_heap();
      exit(0);
    } else if (block != NULL)
      block = get_next_free_block(block);
    else {
      class = get_next_class(class);
      if (class == NULL)
        break;
      else
        block = get_first_free_block_from_class(class);
    }
  }
  // Każdy blok oznaczony jako wolny jest na liście wszystkich wolnych bloków:
  block = heap_start;
  while (block != NULL) {
    if (bt_free(block) && find_in_segregated_list(block) == NULL) {
      printf("brak wolnego bloku na liscie wolnych bloków\n");
      list_the_contents_of_the_heap();
      exit(0);
    } else
      block = bt_next(block);
  }
  // Nie istnieją dwa przyległe do siebie bloki, które są wolne:
  block = heap_start;
  while (block != NULL) {
    if (bt_free(block)) {
      word_t *block_next = bt_next(block);
      if ((block_next != NULL && bt_free(block_next))) {
        printf("obecny blok=%p, i nastepny=%p, obok siebie\n", block,
               block_next);
        list_the_contents_of_the_heap();
        exit(0);
      } else if (block != heap_start && bt_get_prevfree(block)) {
        printf("obecny blok=%p, i poprzedni=%p, obok siebie\n", block,
               bt_prev(block));
        list_the_contents_of_the_heap();
        exit(0);
      } else
        block = bt_next(block);
    } else
      block = bt_next(block);
  }
  // Wskaźnik na poprzedni i następny blok odnoszą się do adresów należących do
  // zarządzanej sterty
  block = heap_start;
  while (block != NULL) {
    word_t *block_prev = NULL;
    if (bt_get_prevfree(block))
      block_prev = bt_prev(block);
    word_t *block_next = bt_next(block);
    if (block_prev != NULL) {
      if (!((heap_start <= block_prev) && (block_prev <= last))) {
        printf("wskaznik na poprzedni blok wykracza poza sterte=%p\n",
               block_prev);
        list_the_contents_of_the_heap();
        exit(0);
      }
    }
    if (block_next != NULL) {
      if (!((heap_start <= block_next) && (block_next <= last))) {
        printf("wskaznik na nastepny blok wykracza poza sterte=%p\n",
               block_next);
        list_the_contents_of_the_heap();
        exit(0);
      }
    }
    block = bt_next(block);
  }
  if (verbose)
    list_the_contents_of_the_heap();
}
