package com.example.backend.business.repository;

import java.util.List;

import org.springframework.data.jpa.repository.JpaRepository;

import com.example.backend.core.domain.Assignees;

public interface AssigneesRepository extends JpaRepository<Assignees, Long> {

    // Find all assignees entries for a given user id
    List<Assignees> findByUser_Id(Long userId);

}
