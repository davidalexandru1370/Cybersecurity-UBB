package com.example.backend.business.repository;

import org.springframework.data.jpa.repository.JpaRepository;

import com.example.backend.core.domain.Assignment;

public interface AssignmentRepository extends JpaRepository<Assignment, Long> {
}
