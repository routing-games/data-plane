/*- /usr/src/sys/net/lisp/maptables.c
 *
 * Copyright (c) 2010 - 2011 The OpenLISP Project
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *  Contributors: 
 *               Luigi Iannone <ggx@openlisp.org>
 *
 * $Id: maptables.c 176 2011-09-22 14:06:30Z ggx $
 *
 */

/* Copyright (c) 1980, 1986, 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)route.c	8.3.1.1 (Berkeley) 2/23/95
 * $FreeBSD: src/sys/net/route.c,v 1.109.2.2 2005/09/26 14:59:12 glebius Exp $
 */

#include "opt_inet.h"
#include "opt_mrouting.h"

#include <sys/types.h>
#include <sys/param.h>
#include <sys/systm.h>
#include <sys/malloc.h>
#include <sys/mbuf.h>
#include <sys/socket.h>
#include <sys/domain.h>
#include <sys/kernel.h>
#include <sys/libkern.h>
#include <sys/syslog.h>

#include <net/if.h>

#include <vm/uma.h>

#include <net/route.h>

#include <netinet/in.h>
#include <netinet/in_var.h>
#include <netinet/ip_var.h>

#include <netinet6/in6_var.h>
#include <netinet/ip6.h>
#include <netinet6/ip6_var.h>

#include <net/lisp/lisp.h>
#include <net/lisp/maptables.h>
#include <net/lisp/maptables_xpg.h>

struct mappingstats mappingstats;

struct radix_node_head *map_tables[MAX_TABLES];

static int  maptrash;	/* mappings not in table but not freed */

static int  map_fix_local_rlocs(struct locator_chain *);

static void map_maskedcopy(struct sockaddr_storage *,  
			   struct sockaddr_storage *, 
			   struct sockaddr_storage *);

static int map_setrlocs(caddr_t *, struct locator_chain **, int, 
			lsbits_type *, int);
static int map_insertrloc(struct locator_chain **, struct sockaddr_storage *,
			  struct rloc_mtx *);
/*y5er*/
static int
map_insertrloc_withsrc( struct locator_chain **, struct sockaddr_storage *,
		struct rloc_mtx *, struct src_locator_chain *);
/*y5er*/
static void  FreeRloc(struct locator_chain * rlocchain);

static void map_copylsbit(struct locator_chain *, lsbits_type *);

static struct mapentry * maplookup(struct sockaddr *, int);

/*
 * Convert a 'struct radix_node *' to a 'struct mapentry *'.
 * The operation can be done safely (in this code) because a
 * 'struct mapentry' starts with two 'struct radix_node''s, the first
 * one representing leaf nodes in the routing tree, which is
 * what the code in radix.c passes us as a 'struct radix_node'.
 *
 * But because there are a lot of assumptions in this conversion,
 * do not cast explicitly, but always use the macro below.
 */
#define RNTOMAP(p)	((struct mapentry *)(p))
 
static uma_zone_t mapzone;		/* Mapping table UMA zone. */

static void
maptables_init(void)
/* 
 * This init both maptables for IPv4 and IPv6 EIDs 
 */
{
 
	mapzone = uma_zcreate("mapentry", sizeof(struct mapentry), NULL, NULL,
	    NULL, NULL, UMA_ALIGN_PTR, 0);

	if (rn_inithead((void**)(void *) &map_tables[IPv4_EIDs_TABLE], 0) == 0){
	        log(LOG_INFO,"WARNING!!! IPv4 MapTable Init KO \n");
	} 
	else {
	  	/* Initialize Expunge Timer */
	        callout_init(&maptable_xpgto_args[IPv4_EIDs_TABLE].timer,
			     CALLOUT_MPSAFE);
		
		maptable_xpgto_args[IPv4_EIDs_TABLE].rnh = map_tables[IPv4_EIDs_TABLE];

		lisp_cache_xpg_to((void *) &maptable_xpgto_args[IPv4_EIDs_TABLE]);

	        log(LOG_INFO,"IPv4 MapTable Init OK \n");
	};
	/*PCD*/
	if (rn_inithead((void**)(void *) &map_tables[IPv4_FW_EIDs_TABLE], 0) == 0){
	        log(LOG_INFO,"WARNING!!! IPv4 Forward MapTable Init KO \n");
	} 
	else {
	  	/* Initialize Expunge Timer */
	        callout_init(&maptable_xpgto_args[IPv4_FW_EIDs_TABLE].timer,
			     CALLOUT_MPSAFE);
		
		maptable_xpgto_args[IPv4_FW_EIDs_TABLE].rnh = map_tables[IPv4_FW_EIDs_TABLE];

		lisp_cache_xpg_to((void *) &maptable_xpgto_args[IPv4_FW_EIDs_TABLE]);

	        log(LOG_INFO,"IPv4 Forward MapTable Init OK \n");
	};

		if (rn_inithead((void**)(void *)&map_tables[IPv6_FW_EIDs_TABLE], 0) == 0){
	        log(LOG_INFO,"WARNING!!! IPv6 MapTable Init KO \n");
	}
	else {
	  	/* Initialize Expunge Timer */
	        callout_init(&maptable_xpgto_args[IPv6_FW_EIDs_TABLE].timer,
			     CALLOUT_MPSAFE);

		maptable_xpgto_args[IPv6_FW_EIDs_TABLE].rnh = map_tables[IPv6_FW_EIDs_TABLE];

		lisp_cache_xpg_to((void *) &maptable_xpgto_args[IPv6_FW_EIDs_TABLE]);

	        log(LOG_INFO,"IPv6 Forward MapTable Init OK \n");
	};

	/*CDP*/
      
        if (rn_inithead((void**)(void *)&map_tables[IPv6_EIDs_TABLE], 0) == 0){
	        log(LOG_INFO,"WARNING!!! IPv6 MapTable Init KO \n");
	}
	else {
	  	/* Initialize Expunge Timer */
	        callout_init(&maptable_xpgto_args[IPv6_EIDs_TABLE].timer,
			     CALLOUT_MPSAFE);

		maptable_xpgto_args[IPv6_EIDs_TABLE].rnh = map_tables[IPv6_EIDs_TABLE];

		lisp_cache_xpg_to((void *) &maptable_xpgto_args[IPv6_EIDs_TABLE]);

	        log(LOG_INFO,"IPv6 MapTable Init OK \n");
	};


} /* maptables_init() */

/*
 * Packet Mapping routines.
 */

static int 
map_fix_local_rlocs(struct locator_chain * lcptr)
{
        int error = EINVAL;
	struct sockaddr_in *rloc_inet = NULL;
	struct sockaddr_in6 *rloc_inet6 = NULL;
	struct in_ifaddr *ia = NULL;
	struct in6_ifaddr *ia6 = NULL;

	while ( lcptr ) {
	       /* Scan the chain checking if the RLOC is the address 
		* of a local interface. 
		*/ 

	        switch (lcptr->rloc.rloc_addr->ss_family) {
      
			case AF_INET:
	
			        rloc_inet = (struct sockaddr_in *) lcptr->rloc.rloc_addr;
				INADDR_TO_IFADDR(rloc_inet->sin_addr, ia); 

				/*
				 * If the address matches, set RLOCF_LIF 
				 * flag and MTU.
				 */
				if ((ia != NULL) &&
				    (IA_SIN(ia)->sin_addr.s_addr == rloc_inet->sin_addr.s_addr)) {
				        lcptr->rloc.rloc_metrix.rlocmtx.flags |= RLOCF_LIF;
					lcptr->rloc.rloc_metrix.rlocmtx.mtu = (ia->ia_ifp)->if_mtu;
					
					error = 0;
  
				};
 
			  
				break;
		    
			case AF_INET6:

			        rloc_inet6 = (struct sockaddr_in6 *) lcptr->rloc.rloc_addr;

			
				ia6 = (struct in6_ifaddr *)ifa_ifwithaddr((struct sockaddr *)(rloc_inet6));



				/*
				 * If the address matches, set RLOCF_LIF 
				 * flag and MTU.
				 */
				if ((ia6 != NULL) &&
				    (IN6_ARE_ADDR_EQUAL(&ia6->ia_addr.sin6_addr,
							&rloc_inet6->sin6_addr))) {

				        lcptr->rloc.rloc_metrix.rlocmtx.flags |= RLOCF_LIF;
					lcptr->rloc.rloc_metrix.rlocmtx.mtu = (ia6->ia_ifp)->if_mtu;
					
					error = 0;
  
				};
				break;

		};

	        lcptr = lcptr->next;

	};

#ifdef LISP_DEBUG
	if (error) {
	        DEBUGLISP("[MAP_FIX_LOCAL_RLOC] No local IF RLOCs Provided for local mapping! \n");
	};
#endif /* LISP_DEBUG */


	return (error);

}  /* map_fix_local_rloc() */



struct locator *
map_findrloc(mapping, rlocaddr)
     struct mapentry * mapping;
     struct sockaddr_storage * rlocaddr;
/* 
 * Scan the RLOC chain for a matching RLOC
 * returns a pointer to the locator on success NULL otherwise
 * The caller should make sure that no changes that can 
 * invalid the pointer can arrive beofre its use.
 */
{
        struct locator_chain * lc = mapping->rlocs;
	int match = 0;

	while ( lc && !match ) {
	       /* Scan the chain looking for matching rloc 
		*/ 

	        if (lc->rloc.rloc_addr->ss_family == rlocaddr->ss_family) {

		        switch (rlocaddr->ss_family) {
      
			case AF_INET:

	 		       if (!bcmp( &((struct sockaddr_in *)lc->rloc.rloc_addr)->sin_addr, &((struct sockaddr_in *)rlocaddr)->sin_addr, sizeof(struct in_addr))) 
	
				       match = 1;

				break;
		    
			case AF_INET6:
			        if ( !bcmp( &((struct sockaddr_in6 *)lc->rloc.rloc_addr)->sin6_addr, &((struct sockaddr_in6 *)rlocaddr)->sin6_addr, sizeof(struct in6_addr)))	
				        match = 1;
				break;

			};

		};

		if (!match)
		        lc = lc->next;

	};

	if (match) {
	  
	        return(&lc->rloc); 

	} else {

	        return(NULL);

	};

}  /* map_findrloc() */
 

int 
map_select_srcrloc(dbmap, drloc,  srloc)
     struct mapentry * dbmap;
     struct locator * drloc;
     struct locator ** srloc;
/* Selection of the source RLOC depends on the 
 * outgoing interface and the AF of the destination RLOC.
 */
{
    struct route_in6 ip6_rt;
	struct sockaddr_storage out_ifa;
    struct in_ifaddr * ia = NULL;
	struct ifnet *ifp = NULL;
	struct rtentry *rt = NULL;
	struct sockaddr_in6 ip6_dst;
	/*PCD */
	int in6_local;
	in6_local = 0;
	/*DPC*/
	/*y5er*/
	int srcloc_count = 0;
	srcloc_count = drloc->rloc_metrix.rlocmtx.src_loc_count;
	struct sockaddr_storage *src_locaddr;
	struct src_locator *src_loc;

	src_loc = &(drloc->src_loc_chain->src_loc); // temporary set, remove latter when LB done
	src_locaddr = src_loc->src_loc_addr; // temporary set, remove latter when LB done
	// src_locaddr = (struct src_loc *)(drloc->src_loc_chain.src_loc)->src_loc_addr ); [old]
	// src_locaddr = drloc->src_loc_chain.src_loc.src_loc_addr; [old]

    printf(" select source rloc  \n");
	int egress_control = 0;
	if ( src_locaddr != NULL && srcloc_count )
	{
		egress_control = 1;

		// we do load balancing for source locator based on the load balancing ring
		// the line for source locator and source locator address could also be removed
		// the logic for load balancing begin here
		struct src_locator_chain *sloc; // source locator that will be used
		struct src_locator_chain *n_sloc; // the current source locator, locator that has been used before
		sloc = c_sloc =  drloc->src_loc_LB_ring.cwr; // point to current used source locator in the ring
		if ( c_sloc && c_sloc->weight <= 0) // if this has been used up, move to next
		{
			sloc = c_sloc->next;
			while  ( (sloc != c_sloc) && (sloc->weight <= 0))  // skip locators that have been used up
			{
				sloc = sloc->next;
			}
			if ( sloc ==  c_sloc) // if all locator in chain have been used up
			{
				reset_load_balancing_for_srcloc(drloc);
				sloc = drloc->src_loc_LB_ring.wr;
			}
		}

		if (sloc)
		{
			src_loc = &(sloc->src_loc); // this has been selected as the source locator
			src_locaddr = src_loc->src_loc_addr;

			sloc->weight = sloc->weight - 1 ; // decrease the weight of used locator
			drloc->src_loc_LB_ring.cwr = sloc->next; // move pointer to the next locator
		}
		// identify the address of source locator will be used for encapsulation
		// use that to select proper locator from the local db at latter step

		// NEED to add a validation to check the source locator found with the output interface of this router
		// validation should be do before !!!

	}

		/*y5er*/

	bzero( &out_ifa, sizeof(struct sockaddr_storage) );

	switch (drloc->rloc_addr->ss_family) {

	case AF_INET:

		ia = ip_rtaddr( *((struct in_addr *)
				  &(((struct sockaddr_in *)drloc->rloc_addr)->sin_addr)), 0);
		/* XXX - 0 is the default FIB */

		if (ia == NULL) {  /* No output interface == no route */
			return ENOATTR;
		};

		out_ifa.ss_family = AF_INET;
		out_ifa.ss_len = sizeof(struct sockaddr_in);
		((struct sockaddr_in *)&out_ifa)->sin_addr =  IA_SIN(ia)->sin_addr;

		break;

	case AF_INET6:
	  
		bzero( &ip6_rt, sizeof(struct route_in6) );

		bzero( &ip6_dst, sizeof(struct sockaddr_in6) );
		ip6_dst.sin6_len = sizeof(struct sockaddr_in6);
		ip6_dst.sin6_family = AF_INET6;
		ip6_dst.sin6_addr = *((struct in6_addr *)&(((struct sockaddr_in6 *)drloc->rloc_addr)->sin6_addr));

		if ((in6_selectroute(&ip6_dst, NULL, NULL, &ip6_rt,&ifp, &rt)) != 0) {
			return ENOATTR;
		};

		if ( rt == NULL )  { /* No route to Destination RLOC */
			return ENOATTR;
		};
		/*PCD*/
		//bcopy( rt->rt_ifa, &out_ifa, 
		//      SS_SIZE(rt->rt_ifa));
		bcopy( (struct sockaddr_in6 *)rt->rt_ifa->ifa_addr, &out_ifa,
                sizeof(struct sockaddr_in6));
		if( IN6_IS_ADDR_LINKLOCAL(&((struct sockaddr_in6 *)rt->rt_ifa->ifa_addr)->sin6_addr))
			in6_local = 1;		
		/*DPC*/	
		RTFREE(rt);

		break;

	default:
		        /* This should really never happen! */
		         panic("[MAP_SELECT_SRCRLOC] AF Not Supported!");
	};

	struct locator_chain * lc = dbmap->rlocs;

	/*y5er*/
	// need to define a better control here
	// prioritize looking up in the source locator chain of the destination locator
	// however, when not found, using the legagy method --- (now for testing we only use one method )

	// find in the locator chain the locator that have same address as the source locator that we identify before
	if ( egress_control ) {
		while( lc && (
				   !(lc->rloc.rloc_addr->ss_family == drloc->rloc_addr->ss_family)
				|| !(lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_UP )
				|| !(lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_LIF)
				|| !(lc->rloc.rloc_metrix.rlocmtx.priority < MAX_RLOC_PRI)
				|| (!in6_local && memcmp( src_locaddr, lc->rloc.rloc_addr, SS_SIZE(lc->rloc.rloc_addr)))
				)
		){

				lc = lc->next;
		};
		if (lc) {
			printf(" source locator select \n");
		}
	}
	else {
		/*PCD*/
		 while( lc && (
						   !(lc->rloc.rloc_addr->ss_family == drloc->rloc_addr->ss_family)
						|| !(lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_UP )
						|| !(lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_LIF)
						|| !(lc->rloc.rloc_metrix.rlocmtx.priority < MAX_RLOC_PRI)
						|| (!in6_local && memcmp( &out_ifa, lc->rloc.rloc_addr, SS_SIZE(lc->rloc.rloc_addr)))
						)
		){

		/* while (lc
			   && !(lc->rloc.rloc_addr->ss_family == drloc->rloc_addr->ss_family)
			   && !(lc->rloc.rloc_metrix.rlocmtx.flags & (RLOCF_UP | RLOCF_LIF))
			   && (lc->rloc.rloc_metrix.rlocmtx.priority < MAX_RLOC_PRI)
			   && (memcmp( &out_ifa, lc->rloc.rloc_addr, SS_SIZE(lc->rloc.rloc_addr)))) { */
			   /* Scan the chain and pick the first that:
			* - Has the same AF
			* - Is a local address
			* - Has a valid priority (i.e. less than 255)
			* - Is the address of the ooutgoing interface
			*/
				lc = lc->next;
		};
		/*DPC*/
	}
	/*y5er*/
	
	if (lc) {

	        *srloc = &(lc->rloc);
  
		lc->rloc.rloc_metrix.rloc_hit++;

		return 0;
	};

	return ENOATTR;

}  /* map_select_srcrloc() */

/*PCD*/
int
map_set_load_balanc_tbl (struct mapentry *rmap) {
	
	struct locator_chain * lc = rmap->rlocs;
	struct weight_rloc *wrc = NULL;
	uint8_t spriority;
	
	while (lc && !(lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_UP)
	          && (lc->rloc.rloc_metrix.rlocmtx.priority < MAX_RLOC_PRI)) {
	       /* scan the chain and pick the first with status up and 
		* with sufficient priority.
		*/
	        lc = lc->next;
	};

	if (lc) {
		/*get list of rloc with sufficient priority */
		spriority = lc->rloc.rloc_metrix.rlocmtx.priority;
		lc = rmap->rlocs;
		while (lc){
			if ( (lc->rloc.rloc_metrix.rlocmtx.flags & RLOCF_UP)
	          && (lc->rloc.rloc_metrix.rlocmtx.priority < MAX_RLOC_PRI)
			  && (lc->rloc.rloc_metrix.rlocmtx.priority == spriority) ) {
			   /* scan the chain and pick the all with status up and 
				* with sufficient priority.
				*/
				if(rmap->load_balanc_tbl.wr == NULL){
					R_Zalloc(wrc, struct weight_rloc *, sizeof(struct weight_rloc));
					rmap->load_balanc_tbl.wr = wrc;
					wrc->next = wrc;
					rmap->load_balanc_tbl.cwr = rmap->load_balanc_tbl.wr;
				}else{
					R_Zalloc(wrc->next, struct weight_rloc *, sizeof(struct weight_rloc));
					wrc = wrc->next;
					wrc->next = rmap->load_balanc_tbl.wr;
				}
				wrc->rloc = &lc->rloc;				
				wrc->weight = lc->rloc.rloc_metrix.rlocmtx.weight;				
			}
	        lc = lc->next;
		};
		return 0;
	};
	rmap->load_balanc_tbl.wr = rmap->load_balanc_tbl.cwr =  NULL;
	return ENOATTR;
}

int
map_reset_load_balanc_tbl (struct mapentry *rmap) {
	
	struct weight_rloc *wrc = rmap->load_balanc_tbl.wr;
	
	if(wrc){
		wrc->weight = wrc->rloc->rloc_metrix.rlocmtx.weight;
		wrc = wrc->next;
		while (wrc != rmap->load_balanc_tbl.wr ) {
			wrc->weight = wrc->rloc->rloc_metrix.rlocmtx.weight; 
			wrc = wrc->next;
		};
		rmap->load_balanc_tbl.cwr = rmap->load_balanc_tbl.wr;
	};
	return 0;
}
/*DPC*/

/*y5er*/
// keep it for later use
int
set_load_balancing_for_srcloc (struct locator_chain * dstloc) {

	struct locator  *dest_rloc = &(dstloc->rloc);
	struct src_locator_chain *lc = dest_rloc->src_loc_chain;

	if (lc)
	{
		dest_rloc->src_loc_LB_ring.wr = lc;
		dest_rloc->src_loc_LB_ring.cwr = lc;
		return 0;
	}
	else
	{
		rmap->load_balanc_tbl.wr = rmap->load_balanc_tbl.cwr =  NULL;
		return ENOATTR;
	}
}
int
reset_load_balancing_for_srcloc (struct locator_chain * dstloc) {

	struct locator  *dest_rloc = &(dstloc->rloc);
	struct src_locator_chain *lc = dest_rloc->src_loc_LB_ring.wr;
	// reset the weight for all locator in the chain
	if ( lc )
	{
		lc->weight = lc->src_loc.src_loc_weight;
		lc = lc->next;
		while ( lc != dest_rloc->src_loc_LB_ring.wr )
		{
			lc->weight = lc->src_loc.src_loc_weight;
			lc = lc->next;
		}

		// reset the cwr to point to the head of the chain wr
		dest_rloc->src_loc_LB_ring.cwr = dest_rloc->src_loc_LB_ring.wr;
	}

	return 0;
}
/*endy5er*/
int 
map_select_dstrloc(rmap, drloc)
      struct mapentry * rmap;
      struct locator ** drloc;
{
	struct weight_rloc *wr;
	struct weight_rloc *swr;
	wr = swr = rmap->load_balanc_tbl.cwr;
	if(swr && swr->weight <= 0){
		wr = swr->next;
		while( (wr != swr) && (wr->weight <=0) )
			wr = wr->next;
		if(wr == swr){
			map_reset_load_balanc_tbl(rmap);

			wr = rmap->load_balanc_tbl.cwr;
		}
	}
	
	if(wr){
		*drloc = wr->rloc; 
		wr->rloc->rloc_metrix.rloc_hit++;
		wr->weight = wr->weight-1;
		rmap->load_balanc_tbl.cwr = wr->next;
		return 0;
	};
	return ENOATTR;

}  /* map_select_dstrloc() */


void
locked_dblookup(emap)
     struct eidmap *emap;
/*
 * Lookups for mappings that are in the Database and locks the entry
 */
{
          emap->mapping = maplookup((struct sockaddr *) &(emap->eid), MAPF_DB);

}   /* locked_dblookup() */


void
dblookup(emap)
     struct eidmap *emap;
/*
 * Lookups for mappings that are in the Database
 */
{
        emap->mapping = maplookup((struct sockaddr *) &(emap->eid), MAPF_DB);

	if (emap->mapping)
	        MAP_UNLOCK(emap->mapping);

}   /* dblookup() */

void
locked_cachelookup(emap)
     struct eidmap *emap;
/*
 * Lookups for mappings that are in the cache and locks the entry
 */
{
        emap->mapping = maplookup((struct sockaddr *) &(emap->eid), 0);


	if ((emap->mapping) && ((emap->mapping->map_flags) & MAPF_DB)) {
	       /* GgX - We found a DB map while we where looking 
		* for a Cache map. Do not return this entry.
		*/

                MAP_UNLOCK(emap->mapping);
		MAP_REMREF(emap->mapping);
		emap->mapping = NULL;

	};

}   /* locked_cachelookup() */

void
cachelookup(emap)
     struct eidmap *emap;
/*
 * Lookups for mappings that are in the cache
 */
{
        emap->mapping = maplookup((struct sockaddr *) &(emap->eid), 0);


	if ((emap->mapping) && ((emap->mapping->map_flags) & MAPF_DB)) {
	       /* GgX - We found a DB map while we where looking 
		* for a Cache map. Do not return this entry.
		*/

                MAP_UNLOCK(emap->mapping);
		MAP_REMREF(emap->mapping);
		emap->mapping = NULL;

	};


	if (emap->mapping)
	        MAP_UNLOCK(emap->mapping);

}   /* cachelookup() */


static struct mapentry *
maplookup(eid, dbflag)
     struct sockaddr *eid;
     int dbflag;
/*
 * Look up the mapping that matches the address given
 * The returned map, if any, is locked.
 */
{
        struct radix_node_head *rnh;
	struct mapentry *map = NULL;	
	struct mapentry *newmap = NULL;
	struct radix_node *rn;
	struct map_addrinfo info;
	struct timeval timenow;

	int    nflags;
	/*PCD*/
	if( (lispfunc != LISP_XTR) && dbflag){
        FW_MAPTABLES(rnh, eid->sa_family);
	}
    else{
		MAPTABLES(rnh, eid->sa_family);
	}
	//	MAPTABLES(rnh, eid->sa_family);
	/*DPC*/
	bzero(&info, sizeof(info));

	/*
	 * Look up the address in the table for that Address Family
	 */
	if (rnh == NULL) {
	       /* GgX - Should I panic here? */
	        (dbflag ? mappingstats.db.miss++ : mappingstats.cache.miss++);
		
		goto miss2;
	}

	RADIX_NODE_HEAD_LOCK(rnh);
	if ((rn = rnh->rnh_matchaddr(eid, rnh)) &&
	    (rn->rn_flags & RNF_ROOT) == 0) {
	
	        /* If we find it and it's not the root node, then
		 * get a reference on the mapentry associated.
		 */
	
		newmap = map = RNTOMAP(rn);
		nflags = map->map_flags ;
	
		if ( dbflag != (nflags & MAPF_DB) ) {
		     
		        /* GgX - A Database map has been asked but the 
                         * map found is in the cache or a cache map 
			 * has been asked but the map found is in the 
			 * database. 
		         */

			newmap = NULL;
			goto miss;

		} else {
		       /* GgX - The mapping that we found is valid 
			*/

		        (dbflag ? mappingstats.db.hit++ : mappingstats.cache.hit++);

			getmicrotime(&timenow);
			newmap->map_lastused = timenow.tv_sec;

		        KASSERT( map == newmap, ("looking the wrong map"));
			MAP_LOCK(newmap);
			MAP_ADDREF(newmap);

		};

		RADIX_NODE_HEAD_UNLOCK(rnh);

	} else {
		/*
		 * Either we hit the root or couldn't find any match,
		 * Which basically means "No Mapping available"
		 */

	miss:
	         (dbflag ? mappingstats.db.miss++ : mappingstats.cache.miss++);
	         RADIX_NODE_HEAD_UNLOCK(rnh);
	
	miss2:	


#ifdef LISP_DEBUG
		 /*
		  * If required, report the failure to syslog.
		  * Works only if lisp debugging is enabled.
		  */
      
		 if (!dbflag && lispdebug) {

		         char addrbuf[SOCK_MAXADDRLEN];

			 switch (eid->sa_family) {
			   
			 case AF_INET6:
			   
			         (void) ip6_sprintf(addrbuf, &(((struct sockaddr_in6 *)eid)->sin6_addr));
				 log(LOG_DEBUG,"[MAPLOOKUP] IPv6 Cache miss for EID: %s\n", addrbuf);
				 break;

			 case AF_INET:
			 default:

			         log(LOG_DEBUG,"[MAPLOOKUP] IPv4 Cache miss for EID: %s\n",
				     inet_ntoa((((struct sockaddr_in *)eid)->sin_addr)));

			 };

		 } else if (dbflag && (lispdebug > LISP_BASIC_DEBUG)) {

		         char addrbuf[SOCK_MAXADDRLEN];

		         switch (eid->sa_family) {

			 case AF_INET6:

				 (void) ip6_sprintf(addrbuf, &(((struct sockaddr_in6 *)eid)->sin6_addr));
				 log(LOG_DEBUG,"[MAPLOOKUP] IPv6 Database miss for EID: %s\n", addrbuf);
				 break;

			 case AF_INET:
			 default:
			   
			         log(LOG_DEBUG,"[MAPLOOKUP] IPv4 Database miss for EID: %s\n",
				     inet_ntoa((((struct sockaddr_in *)eid)->sin_addr)));

			 };

		 };
#endif /* LISP_DEBUG */
	
	};

	if (newmap) {
		MAP_LOCK_ASSERT(newmap);
	};

	return (newmap);

}   /* maplookup() */


static void 
FreeRloc(struct locator_chain * rlocchain)
{
  /* GgX - Remove the whole rloc chain */
      
        while (rlocchain) {
               struct locator_chain * rc;

	       Free(rlocchain->rloc.rloc_addr); /* rloc sockaddr*/
	       rc = rlocchain;
	       rlocchain = rlocchain->next;    
	       Free(rc);                       /* chain node */
        }
} /* FreeRloc */




/*
 * Remove a reference count from an mapentry.
 * If the count gets low enough, take it out of the routing table
 */
void
mapfree(struct mapentry *map)
{
        struct radix_node_head *rnh;

	KASSERT(map != NULL,("%s: NULL map", __func__));  

	MAPTABLES(rnh, ((struct sockaddr_storage *)map_key(map))->ss_family);

	KASSERT(rnh != NULL,("%s: NULL rnh", __func__));  

	MAP_LOCK_ASSERT(map);

	/*             
	 * The callers should use RTFREE_LOCKED() or RTFREE(), so
         * we should come here exactly with the last reference. 
	 */ 
	MAP_REMREF(map);
        if (map->map_refcnt > 0) {
	        printf("%s: %p has %lu refs\n", __func__, map, map->map_refcnt); 
		goto done;
         }   

	/*
         * On last reference give the "close method" a chance
         * to cleanup private state.  This also permits (for  
         * IPv4 and IPv6) a chance to decide if the routing table
         * entry should be purged immediately or at a later time.
	 */                                                     
         if (map->map_refcnt == 0 && rnh->rnh_close)   
                 rnh->rnh_close((struct radix_node *)map, rnh);  
  
	/*
	 * If we are no longer "up" (and ref == 0)
	 * then we can free the resources associated
	 * with the route.
	 */

	if ((map->map_flags & MAPF_UP) == 0) {
		if (map->map_nodes->rn_flags & (RNF_ACTIVE | RNF_ROOT))
			panic ("mapfree !");
		/*
		 * the mapentry must have been removed from the mapping 
		 * table so it is represented in rttrash.. remove that now.
		 */
		maptrash--;


#ifdef	DIAGNOSTIC
		if (map->map_refcnt < 0) {
			printf("mapfree: %p not freed (neg refs)\n", map);
			goto done;
		}
#endif

		/* GgX - RLOCs are separatly alloc'd so free it 
		 * (see map_setrlocs()).
		 */
		FreeRloc(map->rlocs);

		/*
		 * The key is separatly alloc'd so free it (see map_setentry()).
		 */
		Free(map_key(map));
 
		/*
		 * and the rtentry itself of course
		 */
		MAP_LOCK_DESTROY(map);
		uma_zfree(mapzone, map);
		return;
		}
done:
	MAP_UNLOCK(map);
}

static walktree_f_t map_fixchange;

struct mapfc_arg {
	struct mapentry *map0;
	struct radix_node_head *rnh;
};



/*
 * These (questionable) definitions of apparent local variables apply
 * to the next two functions.  XXXXXX!!!
 */
#define	eid	info->mapi_info[MAPX_EID]
#define	rloc	info->mapi_info[MAPX_RLOC]
#define	rlocnum	info->mapi_rloc_count
#define	eidmask	info->mapi_info[MAPX_EIDMASK]
#define	flags	info->mapi_flags
#define	versioning	info->mapi_versioning



int
maprequest(int req, struct map_addrinfo *info, struct mapentry **ret_nmap)
{
  	int error = 0;
	register struct mapentry *mapt;
	register struct radix_node *rn;
	register struct radix_node_head *rnh;
	struct sockaddr_storage *neid;
	struct timeval timenow;
	
#define senderr(x) { error = x ; goto bad; }


	KASSERT(EID,"[MAPREQUEST] NULL pointer to EID!");

	/*
	 * Find the correct mapping tree to use for this Address Family
	 */
	 /*PCD*/
	if( lispfunc == LISP_XTR || !(flags & MAPF_DB) ){
		MAPTABLES(rnh,eid->ss_family);
	}else{
		FW_MAPTABLES(rnh,eid->ss_family);
	}		
	/*DPC*/
	if (rnh == NULL)
		return (EAFNOSUPPORT);
       	RADIX_NODE_HEAD_LOCK(rnh);

	/*
	 * If we are adding a host eid then we don't want to put
	 * a netmask in the tree.
	 */

	switch (req) {
	case MAPM_DELETE:

		/*
		 * Remove the item from the tree and return it.
		 * Complain if it is not there and do no more processing.
		 */
		rn = rnh->rnh_deladdr(eid, eidmask, rnh);
		if (rn == NULL)
			senderr(ESRCH);

		if (rn->rn_flags & (RNF_ACTIVE | RNF_ROOT))
			panic ("maprequest delete");

		mapt = RNTOMAP(rn);
		MAP_LOCK(mapt);
		MAP_ADDREF(mapt);
		mapt->map_flags &= ~MAPF_UP;

		/*
		 * One more mapentry floating around that is not
		 * linked to the routing table. rttrash will be decremented
		 * when MAPFREE(mapt) is eventually called.
		 */
		maptrash++;

		/*
		 * If the caller wants it, then it can have it,
		 * but it's up to it to free the mapentry as we won't be
		 * doing it.
		 */
		if (ret_nmap) {
			*ret_nmap = mapt;
			MAP_UNLOCK(mapt);
		} else		        
			MAPFREE_LOCKED(mapt);
		break;

	case MAPM_ADD:
	       /* Check for flag correctness
		*/
	        if ( (flags & MAPF_ALL) ) {
	                /* All flag cannot be set on adding */
		
#ifdef LISP_DEBUG
		        DEBUGLISP("[MAPREQUEST] Invalid flags! \n");
#endif /* LISP_DEBUG */

			senderr(EINVAL);
		};


	       /* Beside the EID we need at least one rloc
		* Unless it is a negative mapping.
		*/
      	        if ( !eid || 
		     (!(flags & MAPF_NEGATIVE) && (!rloc || !rlocnum)) ||
		     ((flags & MAPF_NEGATIVE) && (rloc || rlocnum))) {

#ifdef LISP_DEBUG
		       DEBUGLISP("[MAPREQUEST] RLOCs Provided for non-Negative mapping! \n");
#endif /* LISP_DEBUG */

		       senderr(EINVAL);
		};

		mapt = uma_zalloc(mapzone, M_NOWAIT | M_ZERO);
		if (mapt == NULL)
			senderr(ENOBUFS);

		MAP_LOCK_INIT(mapt);
		mapt->map_flags = MAPF_UP | flags;

		/*
		 * Add the rloc. Possibly re-malloc-ing the storage for it
		 * also add the map.rlocs if possible.
		 */
		MAP_LOCK(mapt);
		if ((error = map_setentry(mapt, eid)) != 0) {
			Free(map_key(mapt));
			MAP_LOCK_DESTROY(mapt);
			uma_zfree(mapzone, mapt);
#ifdef LISP_DEBUG
			DEBUGLISP("[MAPREQUEST] No Bufs for new entry in MapTables \n");
#endif /* LISP_DEBUG */
			senderr(error);
		}

		/*
		 * point to the (possibly newly malloc'd) eid address.
		 */
		neid = (struct sockaddr_storage *)map_key(mapt);
		
		/*
		 * make sure it contains the value we want (masked if needed).
		 */
		if (eidmask) {
			map_maskedcopy(eid, neid, eidmask);
		} else
			bcopy(eid, neid, eid->ss_len);
		
		rn = rnh->rnh_addaddr(neid, eidmask, rnh, mapt->map_nodes);
		if (rn == NULL) {
 
			senderr(EEXIST);
		};

		if (req == MAPM_ADD && map_mask(mapt) != NULL) {
			struct mapfc_arg arg;
			arg.rnh = rnh;
			arg.map0 = mapt;
			rnh->rnh_walktree_from(rnh, map_key(mapt), 
					       map_mask(mapt),
					       map_fixchange, &arg);
		}


		if ((mapt->rlocs_cnt = rlocnum) && 
		    (error = map_setrlocs((caddr_t*)rloc, &mapt->rlocs, rlocnum,
					  &mapt->rlocs_statusbits, 
					  (mapt->map_flags & MAPF_DB)))) {
		        /* GgX - Error occurred during rloc allocation 
		         * free everything.
		         */
		  
		        rn = rnh->rnh_deladdr(neid, eidmask, rnh);

			Free(map_key(mapt));
		        MAP_LOCK_DESTROY(mapt);
			uma_zfree(mapzone, mapt);
			senderr(error);
		};

		if ( !(mapt->map_flags & MAPF_NEGATIVE) &&
		     (mapt->map_flags & MAPF_DB)  &&
		     (error = map_fix_local_rlocs(mapt->rlocs))) {
		        /* The check for local interface for local RLOCs
			 * failed. Local mapping are allowed only if at
			 * least one RLOC matches the address of an
		         * interface.
		         * Free Everything.
			 */

 		        FreeRloc(mapt->rlocs);
		  
		        rn = rnh->rnh_deladdr(neid, eidmask, rnh);

			Free(map_key(mapt));
		        MAP_LOCK_DESTROY(mapt);
			uma_zfree(mapzone, mapt);
			senderr(error);
		};

		if (flags & MAPF_VERSIONING)
		  mapt->vnum = htons(versioning);
 

		getmicrotime(&timenow);
		mapt->map_lastused = timenow.tv_sec;
		
		/*
		 * actually return a resultant mapentry and
		 * give the caller a single reference.
		 */
		if (ret_nmap) {
			*ret_nmap = mapt;
			MAP_ADDREF(mapt);
		}
		/*PCD*/
		//build load balancing table
		mapt->load_balanc_tbl.wr = mapt->load_balanc_tbl.cwr = NULL;
		if((error = map_set_load_balanc_tbl(mapt))){
			/*one reason to error is not rloc can be used */			
			MAP_UNLOCK(mapt);
			senderr(error);			
		}	
		/*DPC*/
		
		MAP_UNLOCK(mapt);
		break;
	default:
		error = EOPNOTSUPP;
	}

bad:
	RADIX_NODE_HEAD_UNLOCK(rnh);
	return (error);

#undef senderr

} /* End maprequest */

#undef	eid	
#undef	rloc	
#undef	eidmask	
#undef	rlocnum	
#undef 	flags

static int
order_addr(struct sockaddr_storage * saddr1, struct sockaddr_storage * saddr2)
{
        /* The routine must return a value different from zero 
	 * if saddr1 contains an address smaller than saddr2.
	 * Note that IPv4 addresses are considered always as smaller 
	 * than IPv6 addresses.
	 */

         uint8_t * chptr1 = NULL;
         uint8_t * chptr2 = NULL;
	 int length = 0;

	 if ( saddr1->ss_family != saddr2->ss_family ) {
	   
	         if ( saddr1->ss_family == AF_INET )  {
 		        /* saddr1 (IPv4) < saddr2 (IPv6)
			 */

		         return (1);

		 } else {
 		        /* saddr1 (IPv6) > saddr2 (IPv4)
			 */

 		         return (0);

		 };

	 };

	 /* The two addresse are in the same family 
	  */
	 
	 switch (saddr1->ss_family) {

	 case AF_INET:

	   chptr1 = (uint8_t *) &(((struct sockaddr_in *) saddr1)->sin_addr);
	   chptr2 = (uint8_t *) &(((struct sockaddr_in *) saddr2)->sin_addr);
	
	   break;

	 case AF_INET6:

	   chptr1 = (uint8_t *) &(((struct sockaddr_in6 *) saddr1)->sin6_addr);
	   chptr2 = (uint8_t *) &(((struct sockaddr_in6 *) saddr2)->sin6_addr);
	
	   break;

	 };

	 while ( ( *chptr1 == *chptr2 ) && ( length < SS_SIZE(saddr1) ) ) {
	         length++;
		 chptr1++;
		 chptr2++; 
	 };

	 if ( *chptr1 < *chptr2 ) {
	        /* saddr1 < saddr2 
		 */

	         return (1);

	 } else {
	        /* saddr1  > saddr2 
		 */

	         return (0);

	 };


} /* cmp_addr() */

/*y5er*/
static int
map_insertrloc_withsrc(rlocchain, rlocaddr, rlocmtx, srclocchain)
     struct locator_chain ** rlocchain;
     struct sockaddr_storage * rlocaddr;
     struct rloc_mtx * rlocmtx;
     struct src_locator_chain *srclocchain;
/*
 * Inserts a new rloc into a locator_chain ordered by priority and weigth
 * and address if necessary.
 */
{
    struct locator_chain * newrloc, * rcp, * rcpp;
    struct sockaddr_storage * newrlocaddr;
	int diff = 1;

	R_Zalloc(newrloc, struct locator_chain *, sizeof(struct locator_chain));

	if (newrloc == NULL)
		return(ENOBUFS);

	bzero(newrloc, sizeof(struct locator_chain));

	bcopy(rlocmtx, &(newrloc->rloc.rloc_metrix.rlocmtx),sizeof(struct rloc_mtx));

	R_Zalloc(newrlocaddr, struct sockaddr_storage *, SS_SIZE(rlocaddr));

	if (newrlocaddr == NULL) {
		Free(newrloc);
		return(ENOBUFS);
	};

	bcopy(rlocaddr, newrlocaddr, SS_SIZE(rlocaddr));
	newrloc->rloc.rloc_addr = newrlocaddr;

	/*y5er*/
	// include the source locator chain to this rloc (destination locator)
	// we already create the chain when parsing the message
	// we dont do the same way as the newrloacaddr
	// since from the message, the socket structure already presented so we can use pointer to refer to it
	// while the chain is not available in the message, we need to parse and construct
	if ( srclocchain == NULL )
	{
		Free(newrloc);
		return(ENOBUFS);
	}
	newrloc->rloc.src_loc_chain = srclocchain;

	// it is different than the load balancing setting for destination locator
	// where the chain is different, here we using the same chain structure
	// since it is simpler, it is better not create a set load balancing function
	newrloc->rloc.src_loc_LB_ring.cw = srclocchain;
	newrloc->rloc.src_loc_LB_ring.cwr = srclocchain;
	//call to set_load_balancing_for_srcloc
	//here we create the load balancing table for te newrloc , before adding it into the chain
	//the input should be the pointer to newrloc
	// struct locator_chain * newrloc
	// set_load_balancing_for_srcloc(newrloc)
	/*y5er*/

	rcp = *rlocchain;

	/* GgX - Before inserting Check for duplicates
	 * This is not efficient. If we see a lots of RLOCs for one
	 * EID prefix we should change this.
	 */
	while ( rcp && diff) {

	        if ( rcp->rloc.rloc_addr->ss_family == newrloc->rloc.rloc_addr->ss_family)
		  diff = bcmp(rcp->rloc.rloc_addr, newrloc->rloc.rloc_addr, SS_SIZE(rcp->rloc.rloc_addr));
	        else
		        diff = 1;

	        rcp = rcp->next;
	};

	if (!diff) {
	        Free(newrlocaddr);
		Free(newrloc)

#ifdef LISP_DEBUG
		DEBUGLISP("[MAP_INSERTRLOC] Duplicate RLOCs ! \n");
#endif /* LISP_DEBUG */

	        return(EINVAL);
	};

	rcpp = rcp = *rlocchain;

        while ( rcp &&
		(rcp->rloc.rloc_metrix.rlocmtx.priority < newrloc->rloc.rloc_metrix.rlocmtx.priority
		 || (rcp->rloc.rloc_metrix.rlocmtx.priority == newrloc->rloc.rloc_metrix.rlocmtx.priority
		     && order_addr(rcp->rloc.rloc_addr,newrloc->rloc.rloc_addr) ))) {

	        rcpp = rcp;
	        rcp = rcp->next;

	};

        if (rcp == NULL) {
	    /* Either we are queuing at the end of the list
		* or it is the first one
		*/
	        if (rcpp)
		        rcpp->next = newrloc;
	        else
	        	*rlocchain = newrloc;
        } else {
	        if (rcp == rcpp) {
	        /* We are at the head of the chain */
		        *rlocchain = newrloc;
		        newrloc->next = rcp;
	        } else {
	            newrloc->next = rcp;
		        rcpp->next = newrloc;
	        }
        };
        // just for testing purpose
        printf("call to map_insertrloc_withsrc \n");

        return(0);

} /* map_appendrloc */
/*end y5er*/

static int
map_insertrloc(rlocchain, rlocaddr, rlocmtx)
     struct locator_chain ** rlocchain; 
     struct sockaddr_storage * rlocaddr;
     struct rloc_mtx * rlocmtx;
/* 
 * Inserts a new rloc into a locator_chain ordered by priority and weigth
 * and address if necessary.
 */
{
        struct locator_chain * newrloc, * rcp, * rcpp;
   
	struct sockaddr_storage * newrlocaddr;
	int diff = 1;

        R_Zalloc(newrloc, struct locator_chain *, sizeof(struct locator_chain));

	if (newrloc == NULL)
                return(ENOBUFS);

        bzero(newrloc, sizeof(struct locator_chain));

	bcopy(rlocmtx, &(newrloc->rloc.rloc_metrix.rlocmtx), 
	      sizeof(struct rloc_mtx));

        R_Zalloc(newrlocaddr, struct sockaddr_storage *, SS_SIZE(rlocaddr));

	if (newrlocaddr == NULL) {
	        Free(newrloc);
                return(ENOBUFS);
	};
        bcopy(rlocaddr, newrlocaddr, SS_SIZE(rlocaddr));
	newrloc->rloc.rloc_addr = newrlocaddr;

        rcp = *rlocchain;
		
	/* GgX - Before inserting Check for duplicates
	 * This is not efficient. If we see a lots of RLOCs for one 
	 * EID prefix we should change this.
	 */
	while ( rcp && diff) {
	   
	        if ( rcp->rloc.rloc_addr->ss_family == newrloc->rloc.rloc_addr->ss_family) 
		  diff = bcmp(rcp->rloc.rloc_addr, newrloc->rloc.rloc_addr, SS_SIZE(rcp->rloc.rloc_addr));
	        else
		        diff = 1;

	        rcp = rcp->next;
	};
	 
	if (!diff) {
	        Free(newrlocaddr);
		Free(newrloc)

#ifdef LISP_DEBUG
		DEBUGLISP("[MAP_INSERTRLOC] Duplicate RLOCs ! \n");
#endif /* LISP_DEBUG */

	        return(EINVAL);
	};
	 
	rcpp = rcp = *rlocchain;

        while ( rcp && 
		(rcp->rloc.rloc_metrix.rlocmtx.priority < newrloc->rloc.rloc_metrix.rlocmtx.priority 
		 || (rcp->rloc.rloc_metrix.rlocmtx.priority == newrloc->rloc.rloc_metrix.rlocmtx.priority 
		     && order_addr(rcp->rloc.rloc_addr,newrloc->rloc.rloc_addr) ))) {

	        rcpp = rcp;
	        rcp = rcp->next;

	};

        if (rcp == NULL) {
	    /* Either we are queuing at the end of the list
		* or it is the first one 
		*/ 
	        if (rcpp)
		        rcpp->next = newrloc;
	        else
	        	*rlocchain = newrloc;
        } else {
	        if (rcp == rcpp) {
	        /* We are at the head of the chain */
		        *rlocchain = newrloc;
		        newrloc->next = rcp;
	        } else {
	            newrloc->next = rcp;
		        rcpp->next = newrloc;
	        }
        };
	
        return(0);

} /* map_appendrloc */


static void 
map_copylsbit(r_chain, locbits)
     struct locator_chain * r_chain;
     lsbits_type * locbits;
/*
 * Scans the locator chain and make a copy of the status bit of each 
 * RLOC in the Locator Status bits string.
 */
{
        int shift = 0;
	int ct = 0;

        while (r_chain && (ct <= MAXRLOCS)) {
	       
	        if (r_chain->rloc.rloc_metrix.rlocmtx.flags & RLOCF_UP) {
		  
			shift = ct%MAXLBIT;      /* position in the byte */
			*locbits |= htonl(LSBITSHIFT(shift)); 
		};
		ct++;
		r_chain = r_chain->next;    
        };


}  /* map_copylsbit */


static int
map_setrlocs(rlocs, rlocs_chain, rlocs_ct, lsbits, db)
     caddr_t *rlocs;
     struct locator_chain ** rlocs_chain; 
     int rlocs_ct;
     lsbits_type * lsbits;
     int db;
/* 
 * Create the chain of RLOCs.
 * If lsbits is not NULL it creates as well the 
 * Locator Status Bits String 
 */
{
    int rlocs_counter = rlocs_ct;
	struct locator_chain* lc = NULL;
	char * cp =  (char *) rlocs;
	struct rloc_mtx rmtx;
	struct sockaddr_storage * ss;
	int error = 0;
	/* y5er */
	int src_loc_count = 0;
	struct sockaddr_storage * src_ss;
	/* y5er */
	while (rlocs_counter--) {
	  
	      ss = (struct sockaddr_storage *)cp;
		  cp += SS_SIZE(ss);
		  rmtx.priority = *(uint8_t *)cp++;
		  rmtx.weight =  *(uint8_t *)cp++;
		  rmtx.flags =  *(uint16_t *)cp;
		  cp += sizeof(uint16_t);
		  rmtx.mtu =  *(uint32_t *)cp;
		  cp += sizeof(uint32_t);
		  if (db) {  /* No nonce is stored in the DB */
		          if (rmtx.flags & RLOCF_TXNONCE) {
			          FreeRloc(*rlocs_chain);
				  return(EINVAL);
			  };         	  
			  rmtx.tx_nonce.nvalue = 0; 
		  } else {
		          rmtx.tx_nonce.nvalue = (htonl( ((struct nonce_type *)cp)->nvalue & NONCEMASK)) >> 8;
		  };
		  cp += sizeof(struct nonce_type);
		  rmtx.rx_nonce.nvalue = 0; /* Received nonce cannot be set. Just reset it.*/
		  cp += sizeof(struct nonce_type);

		  /*y5er*/
		  // after last nonce is the 32bit value of src_loc_count
		  // the message has been extended to support EC
		  // the normal messages have src_loc_count = 0
		  rmtx.src_loc_count = *(uint32_t *)cp;
		  src_loc_count =  rmtx.src_loc_count;
		  cp += sizeof(uint32_t);

		  // loop through all the source locators
		  if (src_loc_count){
			  // create the source locator chain
			  struct src_locator_chain *srcloc_chain, *rcp, *rcpp;
			  // how about if we not using pointer ?


			  R_Zalloc(srcloc_chain,struct src_locator_chain *,sizeof(struct src_locator_chain));
			  if (srcloc_chain == NULL)
				  return (ENOBUFS);
			  bzero (srcloc_chain,sizeof(struct src_locator_chain));

			  while (src_loc_count--) {

				  struct src_locator_chain *new_srcloc;
				  struct sockaddr_storage *new_srcloc_addr;

				  R_Zalloc(new_srcloc,struct src_locator_chain *,sizeof(struct src_locator_chain));
				  if (new_srcloc == NULL)
					  return (ENOBUFS);
				  bzero (new_srcloc,sizeof(struct src_locator_chain));

				  // get the source locator address from the message
				  src_ss = (struct sockaddr_storage *)cp;
				  // add to the new source locator chain
				  // + first allocate memory,
				  R_Zalloc(new_srcloc_addr, struct sockaddr_storage *,SS_SIZE(src_ss));
				  // + check for error
				  if ( new_srcloc_addr == NULL )
				  {
					  Free(new_srcloc);
					  return (ENOBUFS );
				  }
				  // + get data from the message to new allocated socket address
				  bcopy (src_ss, new_srcloc_addr, SS_SIZE(src_ss));
				  // + add to the locator in the chain
				  new_srcloc->src_loc.src_loc_addr = new_srcloc_addr;

				  // continue parsing the message
				  cp += SS_SIZE(src_ss);  // cp now point to priority
				  // currently we are not using priority, just skip it
				  // rmtx.priority = *(uint8_t *)cp++;
				  cp += sizeof(uint8_t); // cp now point to weight
				  new_srcloc->weight = *(uint8_t *)cp;
				  new_srcloc->src_loc.src_loc_weight = *(uint8_t *)cp;
				  // rmtx.weight  = *(uint8_t *)cp++;
				  cp += sizeof(uint8_t); // cp point to flag
				  //rmtx.flags =  *(uint16_t *)cp;
				  cp += sizeof(uint16_t); // cp point to mtu
				  //rmtx.mtu =  *(uint32_t *)cp;
				  cp += sizeof(uint32_t);
				  cp += sizeof(struct nonce_type);
				  cp += sizeof(struct nonce_type);
				  cp += sizeof(uint32_t);
				  // add the new constructed locator new_srcloc to the locator chain srcloc_chain
				  rcp = rcpp = srcloc_chain;
				  // find the correct position to add
				  while ( rcp && rcp->weight < new_srcloc->weight)
				  {
					  rcpp = rcp;
					  rcp = rcp->next;
				  };
				  // insert the new src loc to the chain
				  if ( rcp == NULL ) // two case could happened
				  {
					  if ( rcpp ) // last element in the chain
						  rcpp->next = new_srcloc;
					  else // the chain is newly construct without any elements
						  srcloc_chain = new_srcloc;
				  }
				  else // rcp != NULL
				  {
					  if ( rcp == rcpp ){ // head of the chain (the chain is not empty as the previous case)
						  srcloc_chain = new_srcloc;
						  new_srcloc->next = rcp;
					  }else { // in the middle of the current chain
						  new_srcloc->next = rcp;
						  rcpp->next = new_srcloc;
					  }
				  }

			  };
			  printf(" number of source locator is %d \n",src_loc_count);
			  if ((error = map_insertrloc_withsrc( &lc, ss, &rmtx, srcloc_chain))) {
				  //Free already allocated RLOCs then return
				  FreeRloc(*rlocs_chain);
				  return(error);
			  };

		  }
		  else  // if there is no src_loc_count, so just insert as normal
		  {
			  if ((error = map_insertrloc( &lc, ss, &rmtx))) {
				  //Free already allocated RLOCs then return
				  FreeRloc(*rlocs_chain);
				  return(error);
			  };
		  }
		  // need to carefully consider to insert node first, then process and insert the source locator into the same node ????
		  // how to know which node is inserted ?
		  /*y5er*/

		  /*
		  if ((error = map_insertrloc( &lc, ss, &rmtx))) {
		            //Free already allocated RLOCs then return
		            FreeRloc(*rlocs_chain);
		            return(error);
		  };         	  
		   */

	};

	*rlocs_chain = lc;

	/* Update Locator Status Bits String if requested 
	 */
	if ( lsbits )
	        map_copylsbit(lc, lsbits); 
	
	return(error);

}  /* map_setrlocs */


/*y5er*/
/* map_set_srcdst_locs */
// modify from the map_setrlocs function above to support EC
/*y5er*/

static int
map_fixchange(struct radix_node *rn, void *vp)
{

  /* This will be filled up when the MAP_CHANGE will be implemented.
   */
        return 0;

} /* map_fixchange */

int
map_setentry(struct mapentry *map, struct sockaddr_storage *eid)

{
        int eidlen = SS_SIZE(eid);

	MAP_LOCK_ASSERT(map);

	if (map->rlocs == NULL ) {
	        /* This is a newly created entry */
		caddr_t new;

		R_Malloc(new, caddr_t, eidlen);

		if (new == NULL)
			return ENOBUFS;
		/*
		 * XXX note, we copy from *eid and not *map_key(map) because
		 * map_add_rloc() can be called to initialize a newly
		 * allocated map entry, in which case map_key(map) == NULL
		 * (and also map->rlocs == NULL).
		 * Map_Free() handles a NULL argument just fine.
		 */
		bcopy(eid, new, eidlen);

		Free(map_key(map));	/* free old block, if any */

		map_key(map) = (struct sockaddr *)new;

	}

	return 0;
}



static void
map_maskedcopy(struct sockaddr_storage *src, struct sockaddr_storage *dst, struct sockaddr_storage *netmask)
{
	register u_char *cp1 = (u_char *)src;
	register u_char *cp2 = (u_char *)dst;
	register u_char *cp3 = (u_char *)netmask;
	u_char *cplim = cp2 + *cp3;
	u_char *cplim2 = cp2 + *cp1;

	*cp2++ = *cp1++; *cp2++ = *cp1++; /* copies sa_len & sa_family */
	cp3 += 2;
	if (cplim > cplim2)
		cplim = cplim2;
	while (cp2 < cplim)
		*cp2++ = *cp1++ & *cp3++;
	if (cp2 < cplim2)
		bzero((caddr_t)cp2, (unsigned)(cplim2 - cp2));
}


SYSINIT(map, SI_SUB_PROTO_DOMAIN, SI_ORDER_ANY, maptables_init, 0);
 
