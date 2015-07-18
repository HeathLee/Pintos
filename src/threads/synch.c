 /* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"

static void priority_donate(struct thread *target, struct thread *source,
  struct lock *lock);

static void nest_donate(struct thread *t, int priority);

static list_less_func cond_compare;

/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value) 
{
  ASSERT (sema != NULL);

  sema->value = value;
  list_init (&sema->waiters);
}

/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  while (sema->value == 0) 
    {
      list_push_back (&sema->waiters, &thread_current ()->elem);
      
      //HEATH: 按优先权排序
      list_sort(&sema->waiters, compare_priority, NULL);
      //END
      
      thread_block ();
    }
  sema->value--;
  intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema) 
{
  enum intr_level old_level;
  bool success;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (sema->value > 0) 
    {
      sema->value--;
      success = true; 
    }
  else
    success = false;
  intr_set_level (old_level);

  return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  old_level = intr_disable ();
  if (!list_empty (&sema->waiters)) 
  {
    list_sort(&sema->waiters, compare_priority, NULL);
    thread_unblock (list_entry (list_pop_front (&sema->waiters),
                                struct thread, elem));
  }
  sema->value++;
  intr_set_level (old_level);
  thread_yield();
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void) 
{
  struct semaphore sema[2];
  int i;

  printf ("Testing semaphores...");
  sema_init (&sema[0], 0);
  sema_init (&sema[1], 0);
  thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
  for (i = 0; i < 10; i++) 
    {
      sema_up (&sema[0]);
      sema_down (&sema[1]);
    }
  printf ("done.\n");
}

/* Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_) 
{
  struct semaphore *sema = sema_;
  int i;

  for (i = 0; i < 10; i++) 
    {
      sema_down (&sema[0]);
      sema_up (&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
  ASSERT (lock != NULL);

  lock->holder = NULL;
  sema_init (&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (!lock_held_by_current_thread (lock));

  //HEATH: 判断当前锁的持有者是否拥有低优先级
  struct thread *current = thread_current();
  struct thread *holder  = lock->holder;
  if (holder && holder->priority < current->priority) {
    priority_donate(holder, current, lock);
  }

  sema_down (&lock->semaphore);
  lock->holder = thread_current ();
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
  bool success;

  ASSERT (lock != NULL);
  ASSERT (!lock_held_by_current_thread (lock));

  success = sema_try_down (&lock->semaphore);
  if (success)
    lock->holder = thread_current ();
  return success;
}

/* Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void
lock_release (struct lock *lock) 
{
  ASSERT (lock != NULL);
  ASSERT (lock_held_by_current_thread (lock));

  lock->holder = NULL;
  sema_up (&lock->semaphore);
  //HEATH： 还原优先级
  struct thread *current = thread_current();
  if (current->is_donated)
  {
    //找出优先级最高的捐赠者
    struct list_elem *e = list_begin(&current->donating_thread_list);
    struct donating_thread *max = list_entry(e, struct donating_thread, elem);
    for (; e != list_end(&current->donating_thread_list);
      e = list_next(e))
    {
      if (list_entry(e, struct donating_thread, elem)->thread->priority >
        max->thread->priority)
        max = list_entry(e, struct donating_thread, elem);
    }

    //找到与释放的锁相同的捐赠者
    for (e = list_begin(&current->donating_thread_list);
      e != list_end(&current->donating_thread_list);
      e = list_next(e))
    {
      struct donating_thread *temp = list_entry(e, struct donating_thread, elem);
      if (temp->lock == lock)
      {
        int i = 63;
        for (; i >= 0; --i)
        {
          if (current->old_priority_array[i] == 1)
          {
            if (temp->lock == max->lock)
            {
              current->priority = i;
              current->old_priority_array[temp->old_priority] = -1;
            } else
            {
              //如果释放的锁的捐赠者不是优先权最高的捐赠者，那么当前线程的优先级
              //不需要发生变化，但是释放的锁的捐赠者的优先级需要从旧优先级数组中删除
              //避免更高优先级的捐赠者释放锁使无法正确恢复优先级
              //example：thread-a（34）由于锁a对main（31）进行捐赠，然后thread-b（36）
              //由于锁b对main（34）进行捐赠，释放锁a时，main优先级不变，但是
              //main的就优先权数组中应该删除34
              current->old_priority_array[temp->thread->priority] = -1;
            }
            list_remove(e);
            int j = temp->thread->count_donating_to_thread;
            for (j -= 1; j >= 0; j--)
            {
              if (temp->thread->donating_to[j] == current)
              {
                temp->thread->donating_to[i] = 0;
                temp->thread->count_donating_to_thread -= 1;
                break;
              }
            }
            free(temp);
            break;
          }
        }
        break;
      }
    }
    if (list_empty(&current->donating_thread_list))
    {
      current->is_donated = false;
      if (current->wanted_priority > -1)
      {
        current->priority = current->wanted_priority;
        current->wanted_priority = -1;
      }
    }
    thread_set_priority(current->priority);
  }
  //END
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock) 
{
  ASSERT (lock != NULL);

  return lock->holder == thread_current ();
}

/* One semaphore in a list. */
struct semaphore_elem 
  {
    struct list_elem elem;              /* List element. */
    struct semaphore semaphore;         /* This semaphore. */
  };

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void
cond_init (struct condition *cond)
{
  ASSERT (cond != NULL);

  list_init (&cond->waiters);
}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock) 
{
  struct semaphore_elem waiter;

  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  
  sema_init (&waiter.semaphore, 0);
  list_push_back (&cond->waiters, &waiter.elem);
  lock_release (lock);
  sema_down (&waiter.semaphore);
  lock_acquire (lock);
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));

  list_sort(&cond->waiters, cond_compare, NULL);
  if (!list_empty (&cond->waiters)) 
    sema_up (&list_entry (list_pop_front (&cond->waiters),
                          struct semaphore_elem, elem)->semaphore);
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);

  while (!list_empty (&cond->waiters))
    cond_signal (cond, lock);
}

static void 
priority_donate(struct thread *target, struct thread *source, struct lock *lock)
{
  struct donating_thread *temp =
    (struct donating_thread *)malloc(sizeof (struct donating_thread));
  temp->thread = source;
  temp->lock = lock;
  temp->old_priority = target->priority;

  bool flag = false; //是否在这个锁上有过捐赠
  struct list_elem *e = list_begin(&target->donating_thread_list);
  for (; e != list_end(&target->donating_thread_list); e = list_next(e))
  {
    if (list_entry(e, struct donating_thread, elem)->lock == lock)
    {
      flag = true;
    }
  }
  if (!flag)
    target->old_priority_array[target->priority] = 1;
  list_push_back(&target->donating_thread_list, &temp->elem);
  source->donating_to[source->count_donating_to_thread] = target;
  source->count_donating_to_thread += 1;

  if (target->count_donating_to_thread > 0)
  {
    nest_donate(target, source->priority);
  } else
  {
    target->priority  = source->priority;
    thread_yield();
  }
  target->is_donated = true;
}

static void
nest_donate(struct thread *t, int priority)
{
  int i = 0;
  if (t->count_donating_to_thread > 0)
  {
    for (;i < t->count_donating_to_thread; i++)
    {
      nest_donate(t->donating_to[i], priority);
      t->donating_to[i]->priority = priority;
    }
    
  }
  t->priority = priority;
  thread_yield();
}

static bool
cond_compare(const struct list_elem *a, const struct list_elem *b, void* aux UNUSED)
{
  return list_entry(list_begin(&list_entry(b, struct semaphore_elem, elem)
    ->semaphore.waiters), struct thread, elem)->priority < 
  list_entry(list_begin(&list_entry(a, struct semaphore_elem, elem)
    ->semaphore.waiters), struct thread, elem)->priority;
}